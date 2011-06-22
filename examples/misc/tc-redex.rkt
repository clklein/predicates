#lang racket
(require redex
         rackunit
         "stlc.rkt")

;; e ::= (λ (x t) e) | (app e e) | (var x)
;;       | (if e then e else e) | true | false
;; t ::= bool | (t -> t)
;; env ::= () | ((x t) env)

(define-language λ-bool
  (e (app e e) (var x) (if e then e else e) (λ (x t) e) true false)
  (t bool x (t -> t))
  (x variable-not-otherwise-mentioned))

(define-metafunction λ-bool
  tc : e (x t) ... -> t or #f
  [(tc true (x t) ...)
   bool]
  [(tc false (x t) ...)
   bool]
  [(tc (if e_1 then e_2 else e_3) (x t) ...)
   t_2
   (where bool (tc e_1 (x t) ...))
   (where t_2 (tc e_2 (x t) ...))
   (where t_2 (tc e_3 (x t) ...))]
  [(tc (var x_1) (x_2 t_2) ... (x_1 t_1) (x_3 t_3) ...)
   t_1
   (side-condition (not (member (term x_1) (term (x_2 ...)))))]
  [(tc (app e_1 e_2) (x t) ...)
   t_3
   (where (t_2 -> t_3) (tc e_1 (x t) ...))
   (where t_2 (tc e_2 (x t) ...))]
  [(tc (λ (x_1 t_1) e) (x_2 t_2) ...)
   (t_1 -> t)
   (where t (tc e (x_1 t_1) (x_2 t_2) ...))]
  [(tc e (x t) ...) #f])

(test-equal (term (tc true)) (term bool))
(test-equal (term (tc (app true false))) (term #f))
(test-equal (term (tc (var x) (x bool))) (term bool))
(test-equal (term (tc (var x))) (term #f))
(test-equal (term (tc (var x) (x bool) (x (bool -> bool)))) (term bool))
(test-equal (term (tc (app (λ (x bool) (var x)) true))) (term bool))
(test-equal (term (tc (app (λ (x bool) (var x)) (app true false)))) (term #f))
(test-equal (term (tc (if true then true else false))) (term bool))
(test-equal (term (tc (if true then true else (λ (x bool) (var x))))) (term #f))

(define (generate-type-check n size)
  (for/and ([in-range n])
    (let* ([res (fixup-vars (generate-lambda size))]
           [exp (second (first res))]
           [type (second (second res))]
           [typed (equal? (term (tc ,exp))
                          (term ,type))])
      (unless typed
        (pretty-print exp)
        (pretty-print res)
        #f))))

(check-not-equal?
 (generate-type-check 100 50)
 #f)