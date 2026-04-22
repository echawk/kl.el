;; kl.el --- KLambda in elisp -*- lexical-binding: t -*-

;; SPDX-License-Identifer: MIT

;; Author: Ethan Hawk
;; Maintainer: Ethan Hawk

;; URL: https://echawk.github.io

;; Version: 1.0.0
;; Package-Requires: ((emacs "24.1"))

;;; Commentary:

;; A *very* simple KLmabda interpreter in Emacs Lisp

;; Page 173 TBoS
(defconst kl-primitives
  '(if and or cond
       intern
       pos tlstr cn str string? n->string string->n
       set value
       simple-error trap-error error-to-string
       cons hd tl cons?
       absvector address-> <-address absvector?
       write-byte read-byte pr open close
       + - * / > < >= <= number?
       defun
       lambda
       let
       =
       eval-kl
       freeze
       type
       get-time

       *standard-input* *standard-output*

       shen.char-stinput? shen.char-stoutput?
       shen.write-string shen.read-unit-string))

(defconst kl-primitive-arities
  '((+ . 2) (- . 2) (* . 2) (/ . 2)
    (= . 2) (< . 2) (> . 2) (<= . 2) (>= . 2)
    (number? . 1) (string? . 1) (cons? . 1) (boolean? . 1)
    (str . 1) (n->string . 1) (string->n . 1)
    (pos . 2) (tlstr . 1)
    (intern . 1) (cn . 2)
    (hd . 1) (tl . 1) (cons . 2)
    (absvector . 1) (address-> . 3) (<-address . 2)
    (absvector? . 1)))

(defvar kl-global-functions (make-hash-table :test 'eq))

(defun kl-execute-primitive (name args)
  (pcase name
    ('+ (apply #'+ args))
    ('- (apply #'- args))
    ('* (apply #'* args))
    ('/ (apply #'/ args))
    ('= (kl-elisp-bool-to-kl-bool (apply #'kl-values-equal-p args)))
    ('< (kl-elisp-bool-to-kl-bool (apply #'< args)))
    ('> (kl-elisp-bool-to-kl-bool (apply #'> args)))
    ('<= (kl-elisp-bool-to-kl-bool (apply #'<= args)))
    ('>= (kl-elisp-bool-to-kl-bool (apply #'>= args)))
    ('number? (kl-elisp-bool-to-kl-bool (numberp (car args))))
    ('string? (kl-elisp-bool-to-kl-bool (stringp (car args))))
    ('cons? (kl-elisp-bool-to-kl-bool (consp (car args))))
    ('boolean? (kl-elisp-bool-to-kl-bool (or (eq (car args) 'true)
                                             (eq (car args) 'false))))
    ('str (kl-value-as-string (car args)))
    ('n->string (number-to-string (car args)))
    ('string->n (let ((s (car args))) (if (zerop (length s)) (error "empty string") (aref s 0))))
    ('pos (char-to-string (aref (car args) (cadr args))))
    ('tlstr (substring (car args) 1))
    ('intern (intern (car args)))
    ('cn (concat (car args) (cadr args)))
    ('hd (car (car args)))
    ('tl (cdr (car args)))
    ('cons (cons (car args) (cadr args)))
    ('absvector (kl-make-vector (car args)))
    ('address-> (aset (car args) (cadr args) (caddr args)))
    ('<-address (aref (car args) (cadr args)))
    ('absvector? (kl-elisp-bool-to-kl-bool (vectorp (car args))))
    (_ (error "Unknown primitive: %s" name))))

(defun kl-apply-primitive (prim arg)
  (pcase prim
    (`(primitive ,name ,arity . ,args)
     (let ((new-args (append args (list arg))))
       (if (= arity 1)
           (kl-execute-primitive name new-args)
         `(primitive ,name ,(1- arity) . ,new-args))))
    (_ (error "Invalid primitive application: %S" prim))))

(defun kl-value-p (v)
  (or
   (eq v 'true)
   (eq v 'false)
   (eq '() v)
   (numberp v)
   (stringp v)))

(defun kl-primitive-p (v) (memq v kl-primitives))

(defun kl-value-as-string (v)
  (cond
   ((eq v 'true) "true")
   ((eq v 'false) "false")
   ((null v) "()")
   ((numberp v) (number-to-string v))
   ((stringp v) v)
   ((symbolp v) (symbol-name v))
   ((consp v)
    (concat "[" (mapconcat #'kl-value-as-string v " ") "]"))
   (t "#<object>")))


(defun kl-make-closure (x body env)
  `(closure ,x ,body ,env))

(defun kl-apply-closure (cl arg)
  (pcase cl
    (`(closure ,params ,body ,env)
     (let ((params (if (listp params) params (list params))))
       (if (= (length params) 1)
           (kl-eval body (kl-extend-env (car params) arg env))
         ;; partial application
         `(closure ,(cdr params) ,body
                   ,(kl-extend-env (car params) arg env)))))))

(defun kl-make-thunk (body env)
  `(thunk ,body ,env))

(defun kl-thaw-thunk (thunk)
  (pcase thunk
    (`(thunk ,body ,env)
     (kl-eval body env))))

(defun kl-apply-env (env y)
  (pcase env
    (`(empty-env) (error "kl-apply-env: '%s' not found in env [%s]. " y env))
    (`(extend-env ,x ,arg ,env)
     (if (equal y x) arg
       (kl-apply-env env y)))))

(defun kl-extend-env (x arg env)
  `(extend-env ,x ,arg ,env))

(defun kl-empty-env ()
  `(empty-env))

(defun kl-make-vector (n)
  (let ((lst-zeros '()))
    (dotimes (_ n)
      (setq lst-zeros (cons 0 lst-zeros)))
    (vconcat lst-zeros)))

(defmacro kl-elisp-bool-to-kl-bool (b)
  `(if ,b 'true 'false))

(defsubst kl-kl-bool-to-elisp-bool (b)
  (cond ((eq b 'true)  t)
        ((eq b 'false) nil)
        (t (error "`b` is not 'true or 'false"))))

(defun kl-values-equal-p (a b)
  (cond
   ((and (symbolp a) (symbolp b)) (eq a b))
   ((and (stringp a) (stringp b)) (string= a b))
   ((and (numberp a) (numberp b)) (= a b))
   ((and (vectorp a) (vectorp b)) (equal a b))
   (t nil)))

(defun kl-get-time (arg env)
  (pcase arg
    ('unix (floor (float-time (current-time))))
    ('run  (- (kl-get-time 'unix env)
              (kl-eval '*init* env)))))

(defun kl-apply1 (fn arg)
  (cond
   ;; closure
   ((and (consp fn) (eq (car fn) 'closure))
    (kl-apply-closure fn arg))

   ;; primitive with arity
   ((and (consp fn) (eq (car fn) 'primitive))
    (kl-apply-primitive fn arg))

   (t
    (error "Not applicable: %S" fn))))

(defun kl-apply (fn args)
  (if (null args)
      fn
    (kl-apply
     (kl-apply1 fn (car args))
     (cdr args))))

(defun kl-eval-cond (clauses env)
  (if (null clauses)
      (error "condition failure")
    (pcase (car clauses)
      (`(,test ,expr)
       (if (kl-kl-bool-to-elisp-bool (kl-eval test env))
           (kl-eval expr env)
         (kl-eval-cond (cdr clauses) env))))))

(defun kl-env-default ()
  (let ((init-env (kl-empty-env)))
    ;; Default variables.
    (dolist (pair
             `((*port* . "1")
               (*porters* . "Ethan Hawk")
               (*langauge* . "Elisp")
               (*version* . "S39.1")
               (*implementation* . ,system-configuration)
               (*release* . ,emacs-version)
               (*os* . ,(symbol-name system-type))
               (*init* . ,(kl-get-time 'unix init-env))
               ))
      (setq init-env (kl-extend-env (car pair) (cdr pair) init-env)))
    init-env))

(defun kl-eval (exp env)
  (pcase exp
    ((pred kl-value-p) exp)

    ((pred symbolp)
     (if-let ((arity (alist-get exp kl-primitive-arities)))
         `(primitive ,exp ,arity)
       (or (gethash exp kl-global-functions)
           (kl-apply-env env exp))))

    (`(lambda ,x ,body)  (kl-make-closure x body env))

    (`(freeze ,body)  (kl-make-thunk body env))
    (`(thaw   ,thunk) (kl-thaw-thunk (kl-eval thunk env)))

    (`(let ,x ,y ,body)
     (kl-eval body
              (kl-extend-env x (kl-eval y env) env)))

    ;; Kept fast-paths for inline operator usage. When curried, they fall through to `(,f . ,args)` below.
    (`(+ ,x ,y) (+ (kl-eval x env) (kl-eval y env)))
    (`(- ,x ,y) (- (kl-eval x env) (kl-eval y env)))
    (`(* ,x ,y) (* (kl-eval x env) (kl-eval y env)))
    (`(/ ,x ,y) (/ (kl-eval x env) (kl-eval y env)))

    (`(= ,x ,y)    (kl-elisp-bool-to-kl-bool
                    (kl-values-equal-p
                     (kl-eval x env)
                     (kl-eval y env))))

    (`(< ,x ,y)    (kl-elisp-bool-to-kl-bool
                    (< (kl-eval x env)  (kl-eval y env))))
    (`(> ,x ,y)    (kl-elisp-bool-to-kl-bool
                    (> (kl-eval x env)  (kl-eval y env))))
    (`(<= ,x ,y)   (kl-elisp-bool-to-kl-bool
                    (<= (kl-eval x env) (kl-eval y env))))
    (`(>= ,x ,y)   (kl-elisp-bool-to-kl-bool
                    (>= (kl-eval x env) (kl-eval y env))))

    (`(number?  ,n) (kl-elisp-bool-to-kl-bool (numberp (kl-eval n env))))
    (`(string?  ,s) (kl-elisp-bool-to-kl-bool (stringp (kl-eval s env))))
    (`(cons?    ,p) (kl-elisp-bool-to-kl-bool (consp   (kl-eval p env))))
    (`(boolean? ,b) (kl-elisp-bool-to-kl-bool
                     (or (eq (kl-eval b env) 'true)
                         (eq (kl-eval b env) 'false))))

    (`(str ,v)       (kl-value-as-string (kl-eval v env)))
    (`(n->string ,n) (number-to-string   (kl-eval n env)))
    (`(string->n ,s)
     (let ((str (kl-eval s env)))
       (if (zerop (length str))
           (error "empty string")
         (aref str 0))))

    ;; Fixed missing evaluations for `s` and `n`
    (`(pos ,s ,n)    (char-to-string     (aref (kl-eval s env) (kl-eval n env))))
    (`(tlstr ,s)     (substring (kl-eval s env) 1))

    (`(intern ,s)    (intern (kl-eval s env)))
    (`(cn ,a ,b)     (concat (kl-eval a env)
                             (kl-eval b env)))

    (`(if ,cond ,conseq ,altern)
     (if (kl-kl-bool-to-elisp-bool (kl-eval cond env))
         (kl-eval conseq env)
       (kl-eval altern env)))

    (`(cond . ,clauses) (kl-eval-cond clauses env))

    (`(and ,e1 ,e2) (if (kl-kl-bool-to-elisp-bool (kl-eval e1 env))
                        (kl-eval e2 env)
                      'false))
    (`(or  ,e1 ,e2) (if (kl-kl-bool-to-elisp-bool (kl-eval e1 env))
                        'true
                      (kl-eval e2 env)))
    (`(not ,e)      (if (kl-kl-bool-to-elisp-bool (kl-eval e env)) 'false 'true))

    (`(hd ,l)   (car (kl-eval l env)))
    (`(tl ,l)   (cdr (kl-eval l env)))

    (`(cons ,v ,l) (cons (kl-eval v env) (kl-eval l env)))

    (`(absvector ,n)
     (kl-make-vector (kl-eval n env)))
    (`(address-> ,vec ,n ,x)
     (aset (kl-eval vec env)
           (kl-eval n   env)
           (kl-eval x   env)))
    (`(<-address ,vec ,n) (aref (kl-eval vec env) (kl-eval n env)))

    (`(absvector? ,v) (kl-elisp-bool-to-kl-bool (vectorp (kl-eval v env))))

    (`(get-time ,arg) (kl-get-time arg env))

    (`(defun ,name ,params ,body)
     (puthash name
              `(closure ,params ,body ,env)
              kl-global-functions)
     name)

    (`(set   ,sym ,val) (kl-extend-env sym val env))
    (`(value ,sym)      (kl-apply-env env sym))

    (`(eval-kl ,exp) (kl-eval exp env))

    (`(,f . ,args)
     (kl-apply
      (kl-eval f env)
      (mapcar (lambda (a) (kl-eval a env)) args)))))

(require 'ert)

(ert-deftest kl-closure ()
  (should
   (eq 7
    (kl-eval '(((lambda x (lambda y (+ x y))) 3) 4) (kl-empty-env)))))

(ert-deftest kl-primitives ()
  (should
   (and
    (string-equal "asdfjkl"
                  (kl-eval '(cn "asdf" "jkl") (kl-env-default)))
    (string-equal "1"
                  (kl-eval '(n->string (hd (cons 1 (cons 2 ())))) (kl-empty-env)))
    (string-equal "str"
                  (kl-eval '(cond ((= 1 2) "num")
                                  ((= "asdf" "asdf") "str"))
                           (kl-empty-env)))

    (equal (list 1 2)
           (kl-eval '(cons 1 (cons 2 ())) (kl-empty-env)))

    (eq (kl-elisp-bool-to-kl-bool t)
        (kl-eval '(or (= 1 2) (= "asdf" "asdf")) (kl-env-default)))
    (eq 6
        (kl-eval (- 10 (* 2 (/ 4 2))) (kl-empty-env)))
    (eq (kl-elisp-bool-to-kl-bool nil)
        (kl-eval '(= 1 "asdf") (kl-empty-env))))))


(ert-deftest kl-freeze-thaw ()
  (should
   (and
    (eq 'true
        (kl-eval
         '(let x (freeze (+ 1 2))
               (and true
                    (= 3 (thaw x))))
         (kl-env-default)))
    (eq 3
        (kl-eval
         '(let t (freeze (+ 1 2))
               (thaw t))
         (kl-env-default))))))

(ert-deftest kl-apply-binary ()
  (should
   (= 3
      (kl-eval '(+ 1 2) (kl-empty-env)))))

(ert-deftest kl-partial-primitive ()
  (should
   (= 3
      (kl-eval '((+ 1) 2) (kl-empty-env)))))

(ert-deftest kl-higher-order ()
  (should
   (= 6
      (kl-eval
       '((lambda (f) (f 2 4))
         (lambda (x y) (+ x y)))
       (kl-empty-env)))))

(ert-deftest kl-eval-kl-application ()
  (should
   (= 3
      (kl-eval
       '(eval-kl (cons + (cons 1 (cons 2 ()))))
       (kl-empty-env)))))

(ert-deftest kl-eval-kl-basic ()
  (should
   (= 3
      (kl-eval
       '(eval-kl (cons + (cons 1 (cons 2 ()))))
       (kl-empty-env)))))

(provide 'kl)

;;; kl.el ends here
