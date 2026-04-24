;; kl-interpreter.el --- CEK-style KL interpreter backend -*- lexical-binding: t; -*-

;; SPDX-License-Identifier: MIT

;;; Commentary:

;; This backend preserves the original KL evaluator as a defunctionalized
;; CEK-style abstract machine: control is the current form/value, environment
;; is an alist, and continuations are explicit stack frames instead of host
;; recursion.

;;; Code:

(defun kl-make-closure (params body env runtime)
  `(closure ,runtime ,(if (listp params) params (list params)) ,body ,env))

(defun kl-make-thunk (body env runtime)
  `(thunk ,runtime ,body ,env))

(defun kl-thaw-thunk (thunk)
  (pcase thunk
    (`(thunk ,runtime ,body ,env)
     (kl-eval body runtime env))
    (_ (kl--signal "Cannot thaw %S" thunk))))

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

(defun kl-interpreter-eval (exp runtime env)
  "Evaluate EXP in RUNTIME using the CEK interpreter backend."
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
                   (setq value (kl-thaw-value value)))
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

(provide 'kl-interpreter)

;;; kl-interpreter.el ends here
