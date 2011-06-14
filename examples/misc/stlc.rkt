#lang racket

(require "../../predicates.rkt"
         rackunit
         redex/reduction-semantics)

;; e ::= (λ (x t) e) | (e e) | (var x]
;;       | (if e then e else e) | true | false
;; t ::= bool | (t -> t)
;; env ::= () | ((x t) env)

(define-predicate
  [(typeof-e (? env) true bool)
   "typeof-true"]
  [(typeof-e (? env) false bool)
   "typeof-false"]
  [(typeof-e (? env) (? e1) bool)
   (typeof-e (? env) (? e2) (? t))
   (typeof-e (? env) (? e3) (? t))
   (typeof-e (? env) (if (? e1) then (? e2) else (? e3)) (? t))
   "typeof-if"]
  [(typeof-e (? env) (? e1) ((? t1) -> (? t2)))
   (typeof-e (? env) (? e2) (? t1))
   (typeof-e (? env) ((? e1) (? e2)) (? t2))
   "typeof-application"]
  [(typeof-e (((? x) (? t)) (? env)) (var (? x)) (? t))
   "typeof-var"]
  [(typeof-e (? env) (var (? y)) (? t))
   (neq (? x) (? y))
   (typeof-e (((? x) (? t1)) (? env)) (var (? y)) (? t))
   "typeof-var-keep-looking"]
  [(typeof-e (((? x) (? t1)) (? env)) (? e) (? t2))
   (typeof-e (? env) (λ ((? x) (? t1)) (? e)) ((? t1) -> (? t2)))
   "typeof-abstraction"])

(define (generate-base pred term csts)
  (match term
    [(list E (lvar x) t)
     (let-values ([(e new-eqs) (generate-base-type E t (cstrs-eqs csts))])
       (struct-copy cstrs csts [eqs (hash-set new-eqs x e)]))]
    [else #f]))

(define (generate-base-type E t cs)
  (match t
    ['bool
     (values (vector-ref (list->vector '(true false)) (random 2)) cs)]
    [(lvar t)
     (let ([x (lvar (gensym 'x))])
       (values x (hash-set cs t 'bool)))]
    [`(,a -> ,b)
     (let ([x (lvar (gensym 'x))])
       (let-values ([(e cs-e) (generate-base-type `((,x ,a) E) b cs)])
         (values `(λ (,x ,a) ,e) cs-e)))]))

(define (generate-lambda size)
  (generate (typeof-e () (? e) bool) size))
     
(check-equal?
 (generate (typeof-e () (λ ((? x) bool) (? x)) bool) 10)
 #f)

(check-not-equal?
 (generate (typeof-e () (λ ((? x) bool) (? x)) (bool -> bool)) 10)
 #f)

(check-equal?
 (generate (typeof-e () ((λ ((? x) bool) (if (? x) then (? x) else false)) false) (bool -> bool)) 10)
 #f)

(check-not-equal?
 (generate (typeof-e () ((λ ((? x) bool) (if (? x) then true else false)) false) bool) 10)
 #f)

(check-equal?
 (generate (typeof-e () ((λ ((? y) (bool)) ((? y) true)) true) (? t)) 5)
 #f)

(check-not-equal?
 (generate (typeof-e ((x bool) ()) (var x) bool) 5)
 #f)

(check-equal?
 (generate (typeof-e ((x (bool-> bool)) ((x bool) ())) (var x) bool) 5)
 #f)

(check-equal?
 (generate (typeof-e () (λ ((? x) bool) true) (bool -> (bool -> bool))) 5)
 #f)

; the money test
(check-equal?
 (generate (typeof-e () (λ ((? x) (bool -> bool)) (λ ((? x) bool) ((var (? x)) true))) (? t)) 10)
 #f)