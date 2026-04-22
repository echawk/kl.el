;; kl.el --- KLambda in Elisp -*- lexical-binding: t; -*-

;; SPDX-License-Identifier: MIT

;; Author: Ethan Hawk
;; Maintainer: Ethan Hawk
;; URL: https://echawk.github.io
;; Version: 1.0.0
;; Package-Requires: ((emacs "24.1"))

;;; Commentary:

;; A small KLambda interpreter in Emacs Lisp.

;;; Code:

(require 'cl-lib)
(require 'ert)
(require 'subr-x)

(define-error 'kl-error "KLambda error")

(cl-defstruct (kl-stream (:constructor kl-stream-create))
  kind
  mode
  path
  buffer
  closed)

(cl-defstruct (kl-runtime (:constructor kl-runtime-create))
  globals
  functions
  types
  stdout
  stdin
  init-time)

(defconst kl-primitive-arities
  '((+ . 2) (- . 2) (* . 2) (/ . 2)
    (= . 2) (< . 2) (> . 2) (<= . 2) (>= . 2)
    (number? . 1) (integer? . 1) (string? . 1) (cons? . 1) (boolean? . 1)
    (str . 1) (n->string . 1) (string->n . 1)
    (pos . 2) (tlstr . 1) (intern . 1) (cn . 2)
    (hd . 1) (tl . 1) (cons . 2)
    (absvector . 1) (address-> . 3) (<-address . 2) (absvector? . 1)
    (open . 2) (close . 1) (pr . 2) (read-byte . 1) (write-byte . 2)
    (bound? . 1) (fn . 1)
    (simple-error . 1) (error-to-string . 1)
    (get-time . 1)
    (shen.char-stinput? . 1) (shen.char-stoutput? . 1)
    (shen.write-string . 2) (shen.read-unit-string . 1)))

(defconst kl-special-forms
  '(and cond defun do eval-kl freeze if lambda let or set thaw trap-error type value))

(defun kl--make-buffer-stream (kind mode &optional path initial-contents)
  (let ((buffer (generate-new-buffer
                 (format " *kl-%s-%s*" kind (or path mode)))))
    (when initial-contents
      (with-current-buffer buffer
        (insert initial-contents)
        (goto-char (point-min))))
    (kl-stream-create :kind kind :mode mode :path path :buffer buffer :closed nil)))

(defun kl-runtime-reset (&optional stdin)
  (let* ((runtime (kl-runtime-create
                   :globals (make-hash-table :test 'eq)
                   :functions (make-hash-table :test 'eq)
                   :types (make-hash-table :test 'eq)
                   :stdout (kl--make-buffer-stream 'standard-output 'out)
                   :stdin (kl--make-buffer-stream 'standard-input 'in nil (or stdin ""))
                   :init-time (floor (float-time (current-time)))))
         (globals (kl-runtime-globals runtime)))
    (dolist (pair
             `((*port* . "1")
               (*porters* . "Ethan Hawk")
               (*language* . "Elisp")
               (*implementation* . ,system-configuration)
               (*release* . ,emacs-version)
               (*os* . ,(symbol-name system-type))
               (*home-directory* . "")
               (*hush* . false)))
      (puthash (car pair) (cdr pair) globals))
    (puthash '*stinput* (kl-runtime-stdin runtime) globals)
    (puthash '*stoutput* (kl-runtime-stdout runtime) globals)
    (puthash '*init* (kl-runtime-init-time runtime) globals)
    runtime))

(defun kl-empty-env ()
  nil)

(defun kl-runtime-output (runtime)
  (with-current-buffer (kl-stream-buffer (kl-runtime-stdout runtime))
    (buffer-string)))

(defun kl-runtime-clear-output (runtime)
  (with-current-buffer (kl-stream-buffer (kl-runtime-stdout runtime))
    (erase-buffer)))

(defun kl-runtime-drain-output (runtime)
  (prog1 (kl-runtime-output runtime)
    (kl-runtime-clear-output runtime)))

(defun kl-runtime-set-input-string (runtime string)
  (let ((old-stream (kl-runtime-stdin runtime))
        (new-stream (kl--make-buffer-stream 'buffer-input 'in nil string)))
    (when (and (kl-stream-p old-stream)
               (buffer-live-p (kl-stream-buffer old-stream)))
      (setf (kl-stream-closed old-stream) t)
      (kill-buffer (kl-stream-buffer old-stream)))
    (setf (kl-runtime-stdin runtime) new-stream)
    (puthash '*stinput* new-stream (kl-runtime-globals runtime))
    new-stream))

(defun kl--signal (format-string &rest args)
  (signal 'kl-error (list (apply #'format format-string args))))

(defun kl--bool (value)
  (if value 'true 'false))

(defun kl--true-p (value)
  (pcase value
    ('true t)
    ('false nil)
    (_ (kl--signal "Expected KL boolean, got %S" value))))

(defun kl--lookup-lexical (env symbol)
  (let ((cell (assq symbol env)))
    (when cell
      (cdr cell))))

(defun kl--bound-lexically-p (env symbol)
  (not (null (assq symbol env))))

(defun kl--global-bound-p (runtime symbol)
  (gethash symbol (kl-runtime-globals runtime) :kl-unbound))

(defun kl--lookup-value (runtime env symbol)
  (cond
   ((memq symbol '(true false)) symbol)
   ((kl--bound-lexically-p env symbol) (kl--lookup-lexical env symbol))
   (t symbol)))

(defun kl--resolve-function (runtime env symbol)
  (cond
   ((kl--bound-lexically-p env symbol)
    (kl--lookup-lexical env symbol))
   ((alist-get symbol kl-primitive-arities)
    `(primitive ,runtime ,symbol ,(alist-get symbol kl-primitive-arities)))
   ((gethash symbol (kl-runtime-functions runtime) nil))
   (t (kl--signal "Not applicable: %S" symbol))))

(defun kl-values-equal-p (a b)
  (equal a b))

(defun kl-value-as-string (value)
  (cond
   ((eq value 'true) "true")
   ((eq value 'false) "false")
   ((null value) "()")
   ((stringp value) value)
   ((numberp value) (number-to-string value))
   ((symbolp value) (symbol-name value))
   ((vectorp value) "#vector")
   ((consp value)
    (format "[%s]" (mapconcat #'kl-value-as-string value " ")))
   ((kl-stream-p value) "#stream")
   (t (format "%S" value))))

(defun kl-render-value (value)
  (cond
   ((stringp value) (prin1-to-string value))
   (t (kl-value-as-string value))))

(defun kl--error-to-string (err)
  (cond
   ((and (consp err) (eq (car err) 'kl-error))
    (let ((payload (cadr err)))
      (if (stringp payload)
          payload
        (error-message-string err))))
   ((and (consp err) (stringp (car err))) (car err))
   ((and (consp err) (symbolp (car err)))
    (error-message-string err))
   (t (format "%S" err))))

(defun kl-make-closure (params body env runtime)
  `(closure ,runtime ,(if (listp params) params (list params)) ,body ,env))

(defun kl-make-thunk (body env runtime)
  `(thunk ,runtime ,body ,env))

(defun kl-thaw-thunk (thunk)
  (pcase thunk
    (`(thunk ,runtime ,body ,env)
     (kl-eval body runtime env))
    (_ (kl--signal "Cannot thaw %S" thunk))))

(defun kl--apply-dispatch (fn arg)
  (cond
   ((and (consp fn) (eq (car fn) 'closure))
    (pcase fn
      (`(closure ,runtime ,params ,body ,env)
       (if (null params)
           (kl--signal "Too many arguments for %S" fn)
         (let ((new-env (cons (cons (car params) arg) env)))
           (if (null (cdr params))
               `(eval ,body ,new-env)
             `(value (closure ,runtime ,(cdr params) ,body ,new-env))))))))
   ((and (consp fn) (eq (car fn) 'primitive))
    (pcase fn
      (`(primitive ,runtime ,name ,arity . ,args)
       (let ((new-args (append args (list arg))))
         (if (= arity 1)
             `(value ,(kl--execute-primitive runtime name new-args))
           `(value (primitive ,runtime ,name ,(1- arity) . ,new-args))))))
    )
   (t
    (kl--signal "Not applicable: %S" fn))))

(defun kl--force-dispatch (value)
  (cond
   ((and (consp value) (eq (car value) 'closure))
    (pcase value
      (`(closure ,_runtime ,params ,body ,env)
       (if (null params)
           `(eval ,body ,env)
         `(value ,value)))))
   ((and (consp value) (eq (car value) 'primitive))
    (pcase value
      (`(primitive ,runtime ,name 0 . ,args)
       `(value ,(kl--execute-primitive runtime name args)))
      (_ `(value ,value))))
   (t
    `(value ,value))))

(defun kl--find-trap-frame (continuations)
  (catch 'trap
    (let ((stack continuations)
          frame)
      (while stack
        (setq frame (pop stack))
        (when (eq (car-safe frame) 'trap)
          (throw 'trap (cons frame stack))))
      nil)))

(defun kl--start-cond (clauses env continuations)
  (if (null clauses)
      (kl--signal "condition failure")
    (pcase (car clauses)
      (`(,test ,expr)
       (list test env (cons `(cond-test ,expr ,(cdr clauses) ,env)
                            continuations)))
      (_
       (kl--signal "Malformed cond clause: %S" (car clauses))))))

(defun kl--stream-open-p (stream)
  (and (kl-stream-p stream)
       (not (kl-stream-closed stream))))

(defun kl--stream-read-char (stream)
  (unless (and (kl--stream-open-p stream)
               (eq (kl-stream-mode stream) 'in))
    (kl--signal "Cannot read from %S" stream))
  (with-current-buffer (kl-stream-buffer stream)
    (if (eobp)
        -1
      (prog1 (char-after)
        (forward-char 1)))))

(defun kl--stream-write-string (stream string)
  (unless (and (kl--stream-open-p stream)
               (eq (kl-stream-mode stream) 'out))
    (kl--signal "Cannot write to %S" stream))
  (with-current-buffer (kl-stream-buffer stream)
    (goto-char (point-max))
    (insert string))
  string)

(defun kl--stream-close (stream)
  (unless (kl--stream-open-p stream)
    (kl--signal "Stream already closed"))
  (when (and (eq (kl-stream-kind stream) 'file)
             (eq (kl-stream-mode stream) 'out))
    (with-current-buffer (kl-stream-buffer stream)
      (write-region (point-min) (point-max) (kl-stream-path stream) nil 'silent)))
  (setf (kl-stream-closed stream) t)
  (when (buffer-live-p (kl-stream-buffer stream))
    (kill-buffer (kl-stream-buffer stream)))
  stream)

(defun kl--open-file-stream (path mode)
  (pcase mode
    ('in
     (with-temp-buffer
       (insert-file-contents-literally path)
       (kl--make-buffer-stream 'file 'in path (buffer-string))))
    ('out
     (kl--make-buffer-stream 'file 'out path))
    (_ (kl--signal "Unsupported open mode %S" mode))))

(defun kl--execute-primitive (runtime name args)
  (pcase name
    ('+ (apply #'+ args))
    ('- (apply #'- args))
    ('* (apply #'* args))
    ('/ (apply #'/ args))
    ('= (kl--bool (apply #'kl-values-equal-p args)))
    ('< (kl--bool (apply #'< args)))
    ('> (kl--bool (apply #'> args)))
    ('<= (kl--bool (apply #'<= args)))
    ('>= (kl--bool (apply #'>= args)))
    ('number? (kl--bool (numberp (car args))))
    ('integer? (kl--bool (and (integerp (car args)) t)))
    ('string? (kl--bool (stringp (car args))))
    ('cons? (kl--bool (consp (car args))))
    ('boolean? (kl--bool (memq (car args) '(true false))))
    ('str (kl-value-as-string (car args)))
    ('n->string (char-to-string (car args)))
    ('string->n (let ((s (car args)))
                  (if (string-empty-p s)
                      (kl--signal "empty string")
                    (aref s 0))))
    ('pos (char-to-string (aref (car args) (cadr args))))
    ('tlstr (substring (car args) 1))
    ('intern (intern (car args)))
    ('cn (concat (car args) (cadr args)))
    ('hd (car (car args)))
    ('tl (cdr (car args)))
    ('cons (cons (car args) (cadr args)))
    ('absvector (make-vector (car args) 0))
    ('address->
     (let ((vec (car args)))
       (aset vec (cadr args) (caddr args))
       vec))
    ('<-address (aref (car args) (cadr args)))
    ('absvector? (kl--bool (vectorp (car args))))
    ('open (kl--open-file-stream (car args) (cadr args)))
    ('close (kl--stream-close (car args)))
    ('pr (prog1 (car args)
           (unless (eq (kl--global-bound-p runtime '*hush*) 'true)
             (kl--stream-write-string (cadr args) (car args)))))
    ('read-byte (kl--stream-read-char (car args)))
    ('write-byte
     (prog1 (car args)
       (kl--stream-write-string (cadr args) (char-to-string (car args)))))
    ('bound? (kl--bool (not (eq (kl--global-bound-p runtime (car args)) :kl-unbound))))
    ('fn (kl--resolve-function runtime nil (car args)))
    ('simple-error (kl--signal "%s" (car args)))
    ('error-to-string (kl--error-to-string (car args)))
    ('get-time
     (pcase (car args)
       ('unix (floor (float-time (current-time))))
       ('run (- (floor (float-time (current-time)))
                (gethash '*init* (kl-runtime-globals runtime))))
       (_ (kl--signal "Unknown get-time argument %S" (car args)))))
    ('shen.char-stinput? (kl--bool (and (kl-stream-p (car args))
                                        (eq (kl-stream-kind (car args)) 'standard-input)
                                        (eq (kl-stream-mode (car args)) 'in))))
    ('shen.char-stoutput? (kl--bool (and (kl-stream-p (car args))
                                         (eq (kl-stream-mode (car args)) 'out))))
    ('shen.write-string
     (prog1 (car args)
       (kl--stream-write-string (cadr args) (car args))))
    ('shen.read-unit-string
     (let ((byte (kl--stream-read-char (car args))))
       (if (= byte -1)
           ""
         (char-to-string byte))))
    (_ (kl--signal "Unknown primitive %S" name))))

(defun kl-eval (exp &optional runtime env)
  (setq runtime (or runtime (kl-runtime-reset)))
  (setq env (or env (kl-empty-env)))
  ;; Use an explicit continuation stack so deep KL terms and KL tail calls
  ;; do not consume the host evaluator's recursion limit.
  (catch 'kl-eval-done
    (let ((mode 'eval)
          (value nil)
          (continuations nil)
          dispatch)
      (while t
        (condition-case err
            (cond
             ((eq mode 'eval)
              (cond
               ((or (numberp exp) (stringp exp) (null exp) (memq exp '(true false)))
                (setq value exp
                      mode 'return))
               ((symbolp exp)
                (setq value (kl--lookup-value runtime env exp)
                      mode 'return))
               ((not (consp exp))
                (setq value exp
                      mode 'return))
               (t
                (pcase exp
                  (`(lambda ,params ,body)
                   (setq value (kl-make-closure params body env runtime)
                         mode 'return))
                  (`(freeze ,body)
                   (setq value (kl-make-thunk body env runtime)
                         mode 'return))
                  (`(thaw ,thunk)
                   (push '(thaw) continuations)
                   (setq exp thunk))
                  (`(let ,name ,binding ,body)
                   (push `(let ,name ,body ,env) continuations)
                   (setq exp binding))
                  (`(if ,test ,then ,else)
                   (push `(if ,then ,else ,env) continuations)
                   (setq exp test))
                  (`(and ,left ,right)
                   (push `(and ,right ,env) continuations)
                   (setq exp left))
                  (`(or ,left ,right)
                   (push `(or ,right ,env) continuations)
                   (setq exp left))
                  (`(cond . ,clauses)
                   (pcase-let ((`(,next-exp ,next-env ,next-k)
                                (kl--start-cond clauses env continuations)))
                     (setq exp next-exp
                           env next-env
                           continuations next-k)))
                  (`(do ,left ,right)
                   (push `(do ,right ,env) continuations)
                   (setq exp left))
                  (`(set ,symbol ,binding)
                   (push `(set ,symbol) continuations)
                   (setq exp binding))
                  (`(value ,symbol)
                   (let ((bound (kl--global-bound-p runtime symbol)))
                     (if (eq bound :kl-unbound)
                         (kl--signal "value of %S is unbound" symbol)
                       (setq value bound
                             mode 'return))))
                  (`(trap-error ,body ,handler)
                   (push `(trap ,handler ,env) continuations)
                   (setq exp body))
                  (`(type ,symbol ,type-value)
                   (puthash symbol type-value (kl-runtime-types runtime))
                   (setq value symbol
                         mode 'return))
                  (`(eval-kl ,inner)
                   (push '(eval-kl) continuations)
                   (setq exp inner))
                  (`(defun ,name ,params ,body)
                   (puthash name
                            (kl-make-closure params body nil runtime)
                            (kl-runtime-functions runtime))
                   (setq value name
                         mode 'return))
                  (`(,fn . ,args)
                   (if (symbolp fn)
                       (let ((callable (kl--resolve-function runtime env fn)))
                         (setq value callable
                               mode 'return)
                         (push `(apply-seq ,args ,env) continuations))
                     (push `(call-fn ,args ,env) continuations)
                     (setq exp fn)))
                  (_
                   (kl--signal "Cannot evaluate %S" exp))))))
             ((eq mode 'return)
              (if (null continuations)
                  (throw 'kl-eval-done value)
                (pcase (pop continuations)
                  (`(thaw)
                   (pcase value
                     (`(thunk ,_runtime ,body ,thunk-env)
                      (setq exp body
                            env thunk-env
                            mode 'eval))
                     (_
                      (kl--signal "Cannot thaw %S" value))))
                  (`(let ,name ,body ,saved-env)
                   (setq env (cons (cons name value) saved-env)
                         exp body
                         mode 'eval))
                  (`(if ,then ,else ,saved-env)
                   (setq env saved-env
                         exp (if (kl--true-p value) then else)
                         mode 'eval))
                  (`(and ,right ,saved-env)
                   (if (kl--true-p value)
                       (setq env saved-env
                             exp right
                             mode 'eval)
                     (setq value 'false)))
                  (`(or ,right ,saved-env)
                   (if (kl--true-p value)
                       (setq value 'true)
                     (setq env saved-env
                           exp right
                           mode 'eval)))
                  (`(cond-test ,then ,remaining ,saved-env)
                   (if (kl--true-p value)
                       (setq env saved-env
                             exp then
                             mode 'eval)
                     (pcase-let ((`(,next-exp ,next-env ,next-k)
                                  (kl--start-cond remaining saved-env continuations)))
                       (setq exp next-exp
                             env next-env
                             continuations next-k
                             mode 'eval))))
                  (`(do ,right ,saved-env)
                   (setq env saved-env
                         exp right
                         mode 'eval))
                  (`(set ,symbol)
                   (puthash symbol value (kl-runtime-globals runtime)))
                  (`(trap ,_handler ,_saved-env))
                  (`(eval-kl)
                   (setq exp value
                         mode 'eval))
                  (`(call-fn ,args ,saved-env)
                   (push `(apply-seq ,args ,saved-env) continuations))
                  (`(apply-seq ,args ,saved-env)
                   (if (null args)
                       (pcase (kl--force-dispatch value)
                         (`(value ,next-value)
                          (setq value next-value))
                         (`(eval ,next-exp ,next-env)
                          (setq exp next-exp
                                env next-env
                                mode 'eval)))
                     (push `(eval-arg ,value () ,(cdr args) ,saved-env) continuations)
                     (setq exp (car args)
                           env saved-env
                           mode 'eval)))
                  (`(eval-arg ,fn ,done ,remaining ,saved-env)
                   (let ((new-done (cons value done)))
                     (if remaining
                         (push `(eval-arg ,fn ,new-done ,(cdr remaining) ,saved-env)
                               continuations)
                       (push `(apply-values ,(nreverse new-done)) continuations)
                       (setq value fn)))
                   (when remaining
                     (setq exp (car remaining)
                           env saved-env
                           mode 'eval)))
                  (`(apply-values ,args)
                   (if (null args)
                       (setq mode 'return)
                     (setq dispatch (kl--apply-dispatch value (car args)))
                     (pcase dispatch
                       (`(value ,next-value)
                        (setq value next-value)
                        (push `(apply-values ,(cdr args)) continuations))
                       (`(eval ,next-exp ,next-env)
                        (setq exp next-exp
                              env next-env
                              mode 'eval)
                        (push `(apply-values ,(cdr args)) continuations))))))))
             (t
              (kl--signal "Unknown evaluator mode %S" mode)))
          (error
           (let ((trap (kl--find-trap-frame continuations)))
             (if trap
                 (pcase-let ((`((trap ,handler ,handler-env) . ,rest) trap))
                   (setq continuations (cons `(apply-values ,(list err)) rest)
                         exp handler
                         env handler-env
                         mode 'eval))
               (signal (car err) (cdr err))))))))))

(defun kl-read-buffer ()
  (let (forms)
    (condition-case nil
        (while t
          (push (read (current-buffer)) forms))
      (end-of-file (nreverse forms)))))

(defun kl-read-file (path)
  (with-temp-buffer
    (insert-file-contents path)
    (kl-read-buffer)))

(defun kl-load-file (path &optional runtime)
  (setq runtime (or runtime (kl-runtime-reset)))
  (dolist (form (kl-read-file path))
    (kl-eval form runtime))
  runtime)

(defun kl-load-files (paths &optional runtime)
  (setq runtime (or runtime (kl-runtime-reset)))
  (dolist (path paths runtime)
    (kl-load-file path runtime)))

(defconst kl-kernel-load-order
  '("ShenOSKernel-41.2/klambda/yacc.kl"
    "ShenOSKernel-41.2/klambda/reader.kl"
    "ShenOSKernel-41.2/klambda/writer.kl"
    "ShenOSKernel-41.2/klambda/sys.kl"
    "ShenOSKernel-41.2/klambda/dict.kl"
    "ShenOSKernel-41.2/klambda/declarations.kl"
    "ShenOSKernel-41.2/klambda/core.kl"
    "ShenOSKernel-41.2/klambda/load.kl"
    "ShenOSKernel-41.2/klambda/macros.kl"
    "ShenOSKernel-41.2/klambda/prolog.kl"
    "ShenOSKernel-41.2/klambda/sequent.kl"
    "ShenOSKernel-41.2/klambda/t-star.kl"
    "ShenOSKernel-41.2/klambda/track.kl"
    "ShenOSKernel-41.2/klambda/types.kl"
    "ShenOSKernel-41.2/klambda/toplevel.kl"
    "ShenOSKernel-41.2/klambda/extension-features.kl"
    "ShenOSKernel-41.2/klambda/extension-expand-dynamic.kl"
    "ShenOSKernel-41.2/klambda/extension-launcher.kl"
    "ShenOSKernel-41.2/klambda/extension-programmable-pattern-matching.kl"
    "ShenOSKernel-41.2/klambda/init.kl"))

(defun kl-load-kernel (&optional runtime)
  (setq runtime (or runtime (kl-runtime-reset)))
  (kl-load-files kl-kernel-load-order runtime))

(defun kl--validator-output (program)
  (with-temp-buffer
    (insert program)
    (call-process-region (point-min) (point-max)
                         (expand-file-name "bins/kl" default-directory)
                         t t nil)
    (buffer-string)))

(defun kl--validator-last-result (program)
  (let* ((output (kl--validator-output program))
         (lines (split-string output "\n" t))
         (result-line (car (last (butlast lines)))))
    (and result-line
         (string-trim
          (replace-regexp-in-string "^[0-9]+ #> " "" result-line)))))

(defmacro kl-with-runtime (bindings &rest body)
  (declare (indent 1))
  `(let* ((runtime (or ,(car bindings) (kl-runtime-reset))))
     ,@body))

(ert-deftest kl-basic-evaluation ()
  (let ((runtime (kl-runtime-reset)))
    (should (= 7 (kl-eval '(((lambda x (lambda y (+ x y))) 3) 4) runtime)))
    (should (equal '(1 2) (kl-eval '(cons 1 (cons 2 ())) runtime)))
    (should (eq 'true (kl-eval '(= (cons 1 (cons 2 ())) (cons 1 (cons 2 ()))) runtime)))
    (should (equal "a" (kl-eval '(n->string 97) runtime)))
    (should (= 65 (kl-eval '(string->n "A") runtime)))
    (should (equal "b" (kl-eval '(pos "abc" 1) runtime)))))

(ert-deftest kl-globals-and-errors ()
  (let ((runtime (kl-runtime-reset)))
    (should (= 1 (kl-eval '(set x 1) runtime)))
    (should (= 1 (kl-eval '(value x) runtime)))
    (should (eq 'true (kl-eval '(bound? x) runtime)))
    (should (string-match-p
             "boom"
             (kl-eval '(trap-error (simple-error "boom")
                                   (lambda E (error-to-string E)))
                      runtime)))))

(ert-deftest kl-zero-arg-defun ()
  (let ((runtime (kl-runtime-reset)))
    (kl-eval '(defun always () 42) runtime)
    (should (= 42 (kl-eval '(always) runtime)))))

(ert-deftest kl-loads-kernel-files ()
  (let ((runtime (kl-runtime-reset)))
    (kl-load-file "ShenOSKernel-41.2/klambda/sys.kl" runtime)
    (should (gethash 'append (kl-runtime-functions runtime)))
    (should (equal '(1 2 3)
                   (kl-eval '(append (cons 1 (cons 2 ())) (cons 3 ())) runtime)))))

(ert-deftest kl-reads-init-kl ()
  (let ((forms (kl-read-file "ShenOSKernel-41.2/klambda/init.kl")))
    (should (consp forms))
    (should (eq 'defun (caar forms)))))

(ert-deftest kl-loads-entire-kernel-definition-set ()
  (let ((runtime (kl-runtime-reset)))
    (kl-load-kernel runtime)
    (should (gethash 'shen.initialise (kl-runtime-functions runtime)))
    (should (gethash 'shen.klfile (kl-runtime-functions runtime)))))

(ert-deftest kl-initialises-shen-runtime ()
  (let ((runtime (kl-runtime-reset)))
    (kl-load-kernel runtime)
    (kl-eval '(shen.initialise) runtime)
    (should (= 2 (kl-eval '(arity cons) runtime)))
    (should (equal "41.2" (kl-eval '(value *version*) runtime)))
    (should (eq 'false (kl-eval '(value shen.*tc*) runtime)))
    (should (= 3
               (kl-eval '(eval (cons + (cons 1 (cons 2 ()))))
                        runtime)))))

(ert-deftest kl-validator-compatibility ()
  (skip-unless (file-executable-p (expand-file-name "bins/kl" default-directory)))
  (let ((runtime (kl-runtime-reset)))
    (dolist (expr '("(+ 1 2)"
                    "(n->string 97)"
                    "(string->n \"A\")"
                    "(pos \"abc\" 1)"
                    "(trap-error (simple-error \"x\") (lambda E (error-to-string E)))"
                    "(set x 1)\n(value x)"
                    "(= (cons 1 (cons 2 ())) (cons 1 (cons 2 ())))"))
      (let* ((forms (with-temp-buffer
                      (insert expr)
                      (goto-char (point-min))
                      (kl-read-buffer)))
             result)
        (setq runtime (kl-runtime-reset))
        (dolist (form forms)
          (setq result (kl-eval form runtime)))
        (should (equal (kl-render-value result)
                       (kl--validator-last-result expr)))))))

(provide 'kl)

;;; kl.el ends here
