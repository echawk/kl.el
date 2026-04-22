;; kl.el --- KLambda in elisp -*- lexical-binding: t -*-

;; SPDX-License-Identifer: MIT

;; Author: Ethan Hawk
;; Maintainer: Ethan Hawk

;; URL: https://echawk.github.io

;; Version: 1.0.0
;; Package-Requires: ((emacs "24.1"))

;;; Commentary:

;; A *very* simple KLmabda interpreter in Emacs Lisp

;; TODO: figure out how to do partial application ~ wrt the builtins and '+'
;; ie. (+ 1) is a function that takes 1 argument.
;; NOTE: This *may* not be required in the new S series kernels... iirc
;; Mark Tarver had noted that the new ports no longer need to support
;; partial application, thus making them easier to port.

;; Still wouldn't hurt to try and implement partial application though,
;; should be a fun exercise.

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

(defvar kl-global-functions (make-hash-table :test 'eq))

(defun kl-primitive-equals (a b)
  (kl-elisp-bool-to-kl-bool
   (kl-values-equal-p a b)))

(defun kl-resolve-primitive (sym)
  (pcase sym
    ('+ #'+)
    ('- #'-)
    ('* #'*)
    ('/ #'/)
    ('< #'<)
    ('> #'>)
    ('<= #'<=)
    ('>= #'>=)
    ('= #'kl-primitive-equals)))

(defun kl-+ (a) (lambda (b) (+ a b)))
(defun kl-- (a) (lambda (b) (- a b)))
(defun kl-* (a) (lambda (b) (* a b)))
(defun kl-/ (a) (lambda (b) (/ a b)))
(defun kl-< (a) (lambda (b) (< a b)))
(defun kl-> (a) (lambda (b) (> a b)))
(defun kl-<= (a) (lambda (b) (<= a b)))
(defun kl->= (a) (lambda (b) (>= a b)))



;; (dolist (pair
;;          '((+ #'kl-+)
;;            (- #'kl--)
;;            (* #'kl-*)
;;            (/ #'kl-/)
;;            (< #'kl-<)
;;            (> #'kl->)
;;            (<= #'kl-<=)
;;            (>= #'kl->=)
;;            (= #'kl-primitive-equals)))

;;   (puthash name
;;            `(closure ,params ,body ,env)
;;            kl-global-functions)
;;   (puthash

;;    )
;;   )


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

;; FIXME: still have to define equality over hash maps.
(defun kl-values-equal-p (a b)
  (cond
   ((and (symbolp a) (symbolp b)) (eq a b))
   ((and (stringp a) (stringp b)) (string= a b))
   ((and (numberp a) (numberp b)) (= a b))
   ((and (vectorp a) (vectorp b)) (equal a b))
   (t nil
      ;;(error "`=` is missing a case for %s and %s" a b)
      )))


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


;;(kl-get-time 'unix (kl-empty-env))
;;(car (kl-eval '*start-time* (kl-env-default)))
;;(kl-eval '*start-time* (kl-env-default))

(defun kl-env-default ()
  (let ((init-env (kl-empty-env)))
    ;; Default variables.
    (dolist (pair
             `((*port*           . "1")
               (*porters*        . "Ethan Hawk")
               (*langauge*       . "Elisp")
               (*version*        . "S41")
               (*implementation* . ,system-configuration)
               (*release*        . ,emacs-version)
               (*os*             . ,(symbol-name system-type))
               (*init*           . ,(kl-get-time 'unix init-env))
               ))
      (setq init-env (kl-extend-env (car pair) (cdr pair) init-env)))
    init-env))

;; FIXME: thoughts on having the dual namespace not suck?
;; (symbol → (fn . closure))
;; (symbol → (val . value))

;; (extend-env 'f '(fn . (closure (x) (+ x 1) env)) env)
;; (extend-env 'x '(val . 42) env)

;; (defun kl-lookup (sym env)
;;   (pcase (kl-apply-env env sym)
;;     (`(fn . ,f) f)
;;     (`(val . ,v) v)
;;     (_ (error "Bad binding"))))

;; (`(,f . ,args)
;;  (let ((fn (kl-lookup-fn f env)))
;;    (kl-apply fn ...)))



;; FIXME: should return both a value (that the expresssion evaluates to)
;; and return an environment, which can then be used to continue to evaluate
;; more expresssions.
(defun kl-eval (exp env)
  (pcase exp
    ;; kl-values evaluate to themselves.
    ((pred kl-value-p) exp)

    ;; They do.
    ((pred symbolp)
     (cond
      ((kl-primitive-p exp)              exp)
      ((gethash exp kl-global-functions) (kl-apply-env env exp))
      (t exp)))

    ;; TODO: ensure that 'x' in this case is a single symbol!
    (`(lambda ,x ,body)  (kl-make-closure x body env))

    (`(freeze ,body)  (kl-make-thunk body env))
    (`(thaw   ,thunk) (kl-thaw-thunk (kl-eval thunk env)))

    (`(let ,x ,y ,body)
     (kl-eval body
              (kl-extend-env x (kl-eval y env) env)))

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

    (`(pos ,s ,n)    (char-to-string     (aref s n)))
    (`(tlstr ,s)     (substring s 1))

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

    (`(absvector? ,v) (vectorp (kl-eval v env)))

    (`(get-time ,arg) (kl-get-time arg env))

    (`(defun ,name ,params ,body)
     (puthash name
              `(closure ,params ,body ,env)
              kl-global-functions)
     name)

    (`(set   ,sym ,val) (kl-extend-env sym (kl-eval val env) env))
    (`(value ,sym)      (kl-apply-env env sym))

    (`(eval-kl ,exp)
     (kl-eval (kl-eval exp env) env))

    (`(,f . ,args)
     (let ((evaled-args (mapcar (lambda (a) (kl-eval a env)) args)))
       (cond
        ;; primitive symbol
        ((and (symbolp f)
              (memq f '(+ - * / < > <= >= =)))
         (apply (kl-resolve-primitive f) evaled-args))

        ;; closure
        (t
         (kl-apply
          (kl-eval f env)
          evaled-args)))))

    ;; (`(,f . ,args)
    ;;  (kl-apply
    ;;   (kl-eval f env)
    ;;   (mapcar (lambda (a) (kl-eval a env)) args)))
    ))


;;(untrace-function #'kl-eval)

(require 'ert)

;;(kl-eval '((lambda (x) x) "asdf") (kl-empty-env))

;;(trace-function #'kl-eval)
(ert-deftest kl-closure ()
  (should
   (eq 7
       (kl-eval '(((lambda x (lambda y (+ x y))) 3) 4) (kl-empty-env)))
   )
  )


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
        (kl-eval '(= 1 "asdf") (kl-empty-env))))

   )
  )

;; (kl-eval '*host* (kl-env-default))


;;(kl-eval '(get-time unix) (kl-empty-env))
;;(kl-eval '(get-time run) (kl-env-default))


;;(kl-eval '*implementation* (kl-empty-env))

;;(kl-eval '(and false true) (kl-empty-env))

;; (kl-eval '(let x 10 (* x (+ 2 3 ))) (kl-env-default))

;;(trace-function #'kl-eval)
;;

;;(kl-eval '(= false (intern "false")) (kl-env-default))

;; (kl-eval 'asdf (kl-empty-env))

;;(kl-eval '(defun xor (X Y) (and (or X Y) (not (and X Y)))) (kl-empty-env))



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

(ert-deftest kl-eval-kl-basic ()
  (should
   (= 3
      (kl-eval
       '(eval-kl (cons + (cons 1 (cons 2 ()))))
       (kl-empty-env)))))

(ert-deftest kl-primitive-higher-order ()
  (should
   (= 7
      (kl-eval
       '((lambda (f) (f 3 4)) +)
       (kl-empty-env)))))

(ert-deftest kl-equals-primitive ()
  (should
   (eq 'true
       (kl-eval '(= 3 3) (kl-empty-env)))))


(provide 'kl)

;;; kl.el ends here
