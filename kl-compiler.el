;; kl-compiler.el --- KL to Emacs Lisp compiler backend -*- lexical-binding: t; -*-

;; SPDX-License-Identifier: MIT

;;; Commentary:

;; This backend compiles KL forms into Emacs Lisp closures that operate against
;; the shared `kl-runtime' model. It can evaluate forms in memory or emit
;; per-file installer .el files for cacheable kernel bootstraps.

;;; Code:

(defvar kl--compiler-counter 0)

(defun kl-make-compiled-function (runtime impl arity &rest args)
  (apply #'list 'compiled runtime impl arity args))

(defun kl-make-compiled-thunk (runtime impl)
  (list 'compiled-thunk runtime impl))

(defun kl--compiler-finalize-function (function)
  (if (or (not kl-byte-compile-generated-functions)
          (byte-code-function-p function))
      function
      (condition-case nil
          (let ((byte-compile-warnings nil)
                (warning-minimum-level :emergency))
            (byte-compile function))
        (error function))))

(defun kl--compiler-tailcall (fn args)
  (list 'compiled-tailcall fn args))

(defun kl--compiler-tailcall-p (value)
  (and (consp value)
       (eq (car value) 'compiled-tailcall)))

(defun kl--compiler-run (value)
  (let ((result value))
    (while (kl--compiler-tailcall-p result)
      (pcase result
        (`(compiled-tailcall ,fn ,args)
         (setq result (kl-apply-function fn args)))))
    result))

(defun kl--compiler-invoke (fn args)
  (kl--compiler-run (kl-apply-function fn args)))

(defun kl--compiler-make-callable (runtime impl arity)
  (let ((compiled-impl (kl--compiler-finalize-function impl)))
    (kl-make-compiled-function
     runtime
     (kl--compiler-finalize-function
      (lambda (&rest args)
        (kl--compiler-run (apply compiled-impl args))))
     arity)))

(defun kl--compiler-make-thunk (runtime impl)
  (let ((compiled-impl (kl--compiler-finalize-function impl)))
    (kl-make-compiled-thunk
     runtime
     (kl--compiler-finalize-function
      (lambda ()
        (kl--compiler-run (funcall compiled-impl)))))))

(defun kl--compiler-normalize-params (params)
  (if (listp params) params (list params)))

(defun kl--compiler-gensym (prefix)
  (intern (format "%s-%d" prefix (cl-incf kl--compiler-counter))))

(defun kl--compiler-env-form (env)
  `(list ,@(mapcar (lambda (binding)
                     `(cons ',(car binding) ,(cdr binding)))
                   env)))

(defun kl--compiler-symbol-form (symbol env)
  (or (cdr (assq symbol env))
      `',symbol))

(defun kl--compiler-compile-cond (clauses env runtime-var tailp)
  (let ((result '(kl--signal "condition failure")))
    (dolist (clause (reverse clauses) result)
      (setq result
            (pcase clause
              (`(,test ,expr)
               `(if (kl--true-p ,(kl--compiler-compile-form test env runtime-var nil))
                    ,(kl--compiler-compile-form expr env runtime-var tailp)
                  ,result))
              (_
               `(kl--signal "Malformed cond clause: %S" ',clause)))))))

(defun kl--compiler-compile-args (args env runtime-var)
  (let (compiled)
    (dolist (arg args (nreverse compiled))
      (push (kl--compiler-compile-form arg env runtime-var nil) compiled))))

(defun kl--compiler-flatten-cons (form)
  (let ((current form)
        elements)
    (while (and (consp current)
                (eq (car current) 'cons)
                (consp (cdr current))
                (consp (cddr current))
                (null (cdddr current)))
      (push (cadr current) elements)
      (setq current (caddr current)))
    (cons (nreverse elements) current)))

(defun kl--compiler-flatten-do (form)
  (let ((current form)
        forms)
    (while (and (consp current)
                (eq (car current) 'do)
                (consp (cdr current))
                (consp (cddr current))
                (null (cdddr current)))
      (push (cadr current) forms)
      (setq current (caddr current)))
    (push current forms)
    (nreverse forms)))

(defun kl--compiler-attach-tail (elements tail)
  (if (null elements)
      tail
    (let ((head (cons (car elements) nil))
          (cursor nil))
      (setq cursor head)
      (dolist (element (cdr elements))
        (setcdr cursor (cons element nil))
        (setq cursor (cdr cursor)))
      (setcdr cursor tail)
      head)))

(defun kl--compiler-literal-value (exp)
  (cond
   ((or (numberp exp)
        (stringp exp)
        (null exp)
        (symbolp exp))
    (cons t exp))
   ((not (consp exp))
    (cons t exp))
   ((and (eq (car exp) 'cons)
         (consp (cdr exp))
         (consp (cddr exp))
         (null (cdddr exp)))
    (pcase-let ((`(,elements . ,tail) (kl--compiler-flatten-cons exp)))
      (let ((values nil)
            (ok t)
            tail-value)
        (dolist (element elements)
          (pcase-let ((`(,element-ok . ,element-value)
                       (kl--compiler-literal-value element)))
            (unless element-ok
              (setq ok nil))
            (push element-value values)))
        (pcase-let ((`(,tail-ok . ,tail-result)
                     (kl--compiler-literal-value tail)))
          (setq tail-value tail-result)
          (unless tail-ok
            (setq ok nil)))
        (if ok
            (cons t (kl--compiler-attach-tail (nreverse values) tail-value))
          '(nil . nil)))))
   (t
    '(nil . nil))))

(defun kl--compiler-build-progn (forms env runtime-var tailp)
  (let ((tail forms)
        compiled)
    (while (cdr tail)
      (push (kl--compiler-compile-form (car tail) env runtime-var nil) compiled)
      (setq tail (cdr tail)))
    (push (kl--compiler-compile-form (car tail) env runtime-var tailp) compiled)
    (setq compiled (nreverse compiled))
    (if (cdr compiled)
        `(progn ,@compiled)
      (car compiled))))

(defun kl--compiler-call-form (fn args env runtime-var tailp)
  (let ((fn-form (if (and (symbolp fn) (not (assq fn env)))
                     `(kl--resolve-function ,runtime-var nil ',fn)
                   (kl--compiler-compile-form fn env runtime-var nil)))
        (arg-forms (kl--compiler-compile-args args env runtime-var)))
    (if tailp
        `(kl--compiler-tailcall ,fn-form (list ,@arg-forms))
      `(kl--compiler-invoke ,fn-form (list ,@arg-forms)))))

(defun kl--compiler-compile-application (fn args env runtime-var tailp)
  (kl--compiler-call-form fn args env runtime-var tailp))

(defun kl--compiler-compile-form (exp env runtime-var &optional tailp)
  (cond
   ((numberp exp) exp)
   ((stringp exp) exp)
   ((null exp) ''())
   ((memq exp '(true false)) `',exp)
   ((symbolp exp) (kl--compiler-symbol-form exp env))
   ((not (consp exp)) `',exp)
   ((and (eq (car exp) 'cons)
         (consp (cdr exp))
         (consp (cddr exp))
         (null (cdddr exp)))
    (pcase-let ((`(,literalp . ,literal-value) (kl--compiler-literal-value exp)))
      (if literalp
          `',literal-value
        (pcase-let ((`(,elements . ,tail) (kl--compiler-flatten-cons exp)))
          (let ((compiled-elements (kl--compiler-compile-args elements env runtime-var)))
            (if (null tail)
                `(list ,@compiled-elements)
              `(append (list ,@compiled-elements)
                       ,(kl--compiler-compile-form tail env runtime-var nil))))))))
   (t
    (pcase exp
      (`(lambda ,params ,body)
       (let* ((params-list (kl--compiler-normalize-params params))
              (arg-vars (mapcar (lambda (_param) (kl--compiler-gensym "kl-arg"))
                                params-list))
              (lambda-env (append (cl-mapcar #'cons params-list arg-vars) env)))
         `(kl--compiler-make-callable
           ,runtime-var
           (lambda ,arg-vars
             ,(kl--compiler-compile-form body lambda-env runtime-var t))
           ,(length params-list))))
      (`(freeze ,body)
       `(kl--compiler-make-thunk
         ,runtime-var
         (lambda ()
           ,(kl--compiler-compile-form body env runtime-var t))))
      (`(thaw ,thunk)
       `(kl-thaw-value ,(kl--compiler-compile-form thunk env runtime-var nil)))
      (`(let ,name ,binding ,body)
       (let ((var (kl--compiler-gensym (format "kl-let-%s" name))))
         `(let ((,var ,(kl--compiler-compile-form binding env runtime-var nil)))
            ,(kl--compiler-compile-form body
                                        (cons (cons name var) env)
                                        runtime-var
                                        tailp))))
      (`(if ,test ,then ,else)
       `(if (kl--true-p ,(kl--compiler-compile-form test env runtime-var nil))
            ,(kl--compiler-compile-form then env runtime-var tailp)
          ,(kl--compiler-compile-form else env runtime-var tailp)))
      (`(and ,left ,right)
       `(if (kl--true-p ,(kl--compiler-compile-form left env runtime-var nil))
            ,(kl--compiler-compile-form right env runtime-var tailp)
          'false))
      (`(or ,left ,right)
       `(if (kl--true-p ,(kl--compiler-compile-form left env runtime-var nil))
            'true
          ,(kl--compiler-compile-form right env runtime-var tailp)))
      (`(cond . ,clauses)
       (kl--compiler-compile-cond clauses env runtime-var tailp))
      (`(do ,left ,right)
       (kl--compiler-build-progn
        (kl--compiler-flatten-do exp)
        env
        runtime-var
        tailp))
      (`(set ,symbol ,binding)
       (let ((var (kl--compiler-gensym "kl-set")))
         `(let ((,var ,(kl--compiler-compile-form binding env runtime-var nil)))
            (puthash ',symbol ,var (kl-runtime-globals ,runtime-var))
            ,var)))
      (`(value ,symbol)
       `(let ((bound (kl--global-bound-p ,runtime-var ',symbol)))
          (if (eq bound :kl-unbound)
              (kl--signal "value of %S is unbound" ',symbol)
            bound)))
      (`(trap-error ,body ,handler)
       `(condition-case err
            (kl--compiler-run
             ,(kl--compiler-compile-form body env runtime-var t))
          (error
           ,(if tailp
                `(kl--compiler-tailcall
                  ,(kl--compiler-compile-form handler env runtime-var nil)
                  (list err))
              `(kl--compiler-invoke
                ,(kl--compiler-compile-form handler env runtime-var nil)
                (list err))))))
      (`(type ,symbol ,type-value)
       `(progn
          (puthash ',symbol ',type-value (kl-runtime-types ,runtime-var))
          ',symbol))
      (`(eval-kl ,inner)
       `(kl-eval
         ,(kl--compiler-compile-form inner env runtime-var nil)
         ,runtime-var
         ,(kl--compiler-env-form env)))
      (`(defun ,name ,params ,body)
       (let* ((params-list (kl--compiler-normalize-params params))
              (arg-vars (mapcar (lambda (_param) (kl--compiler-gensym "kl-arg"))
                                params-list))
              (lambda-env (cl-mapcar #'cons params-list arg-vars)))
         `(progn
            (puthash ',name
                     (kl--compiler-make-callable
                      ,runtime-var
                      (lambda ,arg-vars
                        ,(kl--compiler-compile-form body lambda-env runtime-var t))
                      ,(length params-list))
                     (kl-runtime-functions ,runtime-var))
            ',name)))
      (`(,fn . ,args)
       (kl--compiler-compile-application fn args env runtime-var tailp))
      (_
       `(kl--signal "Cannot evaluate %S" ',exp))))))

(defun kl-compiler-eval (exp runtime env)
  "Evaluate EXP in RUNTIME using the compiler backend."
  (let ((kl--compiler-counter 0))
    (let* ((runtime-var (kl--compiler-gensym "kl-runtime"))
           (compiled-env (mapcar (lambda (binding)
                                   (cons (car binding)
                                         (kl--compiler-gensym
                                          (format "kl-env-%s" (car binding)))))
                                 env))
           (form (kl--compiler-compile-form exp compiled-env runtime-var t))
           (bindings `((,runtime-var ',runtime)
                       ,@(cl-mapcar (lambda (binding compiled-binding)
                                      `(,(cdr compiled-binding) ',(cdr binding)))
                                    env compiled-env))))
      (kl--compiler-run (eval `(let ,bindings ,form) t)))))

(defun kl--compiler-file-stem (path)
  (file-name-sans-extension (file-name-nondirectory path)))

(defun kl--compiler-output-file (source directory)
  (expand-file-name (concat (kl--compiler-file-stem source) ".el")
                    directory))

(defun kl--compiler-installer-symbol (path)
  (intern (format "klc--install-%s-%s"
                  (kl--compiler-file-stem path)
                  (substring (secure-hash 'sha1 (expand-file-name path)) 0 8))))

(defun kl--compiler-feature-symbol (path)
  (intern (format "klc-%s-%s"
                  (kl--compiler-file-stem path)
                  (substring (secure-hash 'sha1 (expand-file-name path)) 0 8))))

(defun kl--compiler-output-stale-p (source output)
  (or (not (file-exists-p output))
      (file-newer-than-file-p source output)))

(defun kl--compiler-byte-compile-output (output)
  (when kl-byte-compile-generated-files
    (condition-case nil
        (let ((byte-compile-warnings nil)
              (warning-minimum-level :emergency))
          (byte-compile-file output))
      (error nil))))

(defun kl-compiler-load-file (source runtime &optional directory)
  "Install SOURCE into RUNTIME via a cached generated installer.

When DIRECTORY is non-nil, use it for emitted per-file `.el' installers.
Otherwise fall back to `kl-compiler-cache-directory'."
  (let* ((source (expand-file-name source))
         (directory (or directory
                        kl-compiler-cache-directory
                        (file-name-directory source)))
         (output (kl--compiler-output-file source directory))
         (installer (kl--compiler-installer-symbol source)))
    (make-directory directory t)
    (when (kl--compiler-output-stale-p source output)
      (kl-compile-file-to-el source output)
      (kl--compiler-byte-compile-output output))
    (load (file-name-sans-extension output) nil t)
    (funcall installer runtime)
    runtime))

(defun kl-compile-file-to-el (source output)
  "Compile SOURCE .kl file into OUTPUT .el installer."
  (let ((kl--compiler-counter 0))
    (let* ((source (expand-file-name source))
           (output (expand-file-name output))
           (installer (kl--compiler-installer-symbol source))
           (feature (kl--compiler-feature-symbol source))
           (forms (kl-read-file source)))
      (make-directory (file-name-directory output) t)
      (with-temp-file output
        (insert (format ";; %s --- generated from %s -*- lexical-binding: t; -*-\n\n"
                        (file-name-nondirectory output)
                        (file-name-nondirectory source)))
        (insert ";; SPDX-License-Identifier: MIT\n\n")
        (insert "(require 'kl)\n\n")
        (prin1
         `(defun ,installer (runtime)
            ,(format "Install compiled KL definitions from `%s' into RUNTIME." source)
            ,@(mapcar (lambda (form)
                        (kl--compiler-compile-form form nil 'runtime))
                      forms)
            runtime)
         (current-buffer))
        (insert "\n\n")
        (prin1 `(provide ',feature) (current-buffer))
        (insert "\n"))
      output)))

(defun kl-compile-kernel-to-directory (directory)
  "Compile the configured KL kernel into DIRECTORY as per-file .el installers."
  (dolist (path kl-kernel-load-order)
    (kl-compile-file-to-el
     path
     (kl--compiler-output-file path directory))))

(provide 'kl-compiler)

;;; kl-compiler.el ends here
