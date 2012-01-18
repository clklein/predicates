#lang racket

(require "../../predicates.rkt"
         rackunit
         redex/reduction-semantics)

(provide generate-boolean
         generate-lambda
         fixup-vars
         (all-from-out "../../predicates.rkt"))

;; e ::= (λ (x t) e) | (app e e) | (var x)
;;       | (if0 e e e) | true | false
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
   (typeof-e (? env) (if0 (? e1) (? e2) (? e3)) (? t))
   "typeof-if"]
  [(typeof-e (? env) (? e1) ((? t1) -> (? t2)))
   (typeof-e (? env) (? e2) (? t1))
   (typeof-e (? env) (app (? e1) (? e2)) (? t2))
   "typeof-application"]
  [(typeof-var (? env) (? x) (? t))
   (typeof-e (? env) (var (? x)) (? t))
   "typeof-var"]
  [(typeof-e (((? x) (? t1)) (? env)) (? e) (? t2))
   (typeof-e (? env) (λ ((? x) (? t1)) (? e)) ((? t1) -> (? t2)))
   "typeof-abstraction"]
  [bounding-rules "typeof-true" "typeof-var" "typeof-abstraction"])

(define-predicate
  [(typeof-var (((? x) (? t)) (? env)) (? x) (? t))
   "found-var"]
  [(typeof-var (? env) (? y) (? t))
   (neq (? x) (? y))
   (typeof-var (((? x) (? t1)) (? env)) (? y) (? t))
   "keep-looking"]
  [bounding-rules "found-var" "keep-looking"])

(define (generate-base pred term csts)
  (cond [(eq? pred typeof-e)
         (match term
           [(list E (lvar x) t) 
            (let-values ([(e new-eqs) (generate-base-type E t (cstrs-eqs csts))])
              (struct-copy cstrs csts [eqs (hash-set new-eqs x e)]))]
           [else #f])]
        [(eq? pred typeof-var)
         (match term
           [(list E (lvar x) t)
            (let ([var (var-search E t)]
                  [eqs (cstrs-eqs csts)])
              (if var
                  (struct-copy cstrs csts [eqs (if (equal? x var) eqs (hash-set eqs var (lvar x)))])
                  #f))]
           [else #f])]
        [else (error 'generate-base "unexpected pred ~s" pred)]))

(define (var-search E t)
  (define (t? a-t) (equal? t a-t))
  (match E
    [`((,(lvar y) ,(? t? x-t)) ,etc) 
       y]
    [`((,y ,some-t) ,etc) (var-search etc t)]
    [else #f]))

(define (generate-base-type E t cs)
  (match t
    ['bool
     (values (vector-ref (list->vector '(true false)) (random 2)) cs)]
    [(lvar t)
     (values 'true (hash-set cs t 'bool))]
    [`(,a -> ,b)
     (let ([x (lvar (gensym 'x))])
       (let-values ([(e cs-e) (generate-base-type `((,x ,a) E) b cs)])
         (values `(λ (,x ,a) ,e) cs-e)))]))

(define (generate-lambda size)
  (parameterize ([user-goal-solver generate-base])
    (fixup-vars (generate (typeof-e () (? e) (? t)) size))))

(define (generate-boolean size)
  (parameterize ([user-goal-solver generate-base])
    (fixup-vars (generate (typeof-e () (? e) bool) size))))
     
(define (generates-well-typed? size tries)
  (for/and ([_ (in-range tries)])
    (match (fixup-vars (generate-lambda size))
      [`( (e ,e) (t ,t) )
       (unless (generate (typeof-e () ,e ,t) +inf.0)
         (pretty-print e)
         (pretty-print t)
         false)]
      [`( (t ,t) (e ,e) )
       (unless (generate (typeof-e () ,e ,t) +inf.0)
         (pretty-print e)
         (pretty-print t)
         false)])))

(define (fixup-vars exp)
  (let ([vars (hash)]
        [var-inc 0])
    (define (new-var sym)
      (let ([prefix (substring (symbol->string sym) 0 1)])
        (set! vars (hash-set vars sym (string->symbol (string-append prefix "_" (number->string var-inc)))))
        (set! var-inc (+ var-inc 1))
        (hash-ref vars sym)))
    (let recur ([e exp])
      (match e
        [(lvar x)
         (hash-ref vars x (lambda () (new-var x)))]
        [`(,es ...)
         (for/list ([e es]) (recur e))]
        [else e]))))

(check-equal?
 (generate (typeof-e () (λ ((? x) bool) (var (? x))) bool) +inf.0)
 #f)

(check-not-equal?
 (generate (typeof-e () (λ (x bool) (var x)) (bool -> bool)) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () (app (λ ((? x) bool) (if0 (var (? x)) (var (? x)) false)) false) (bool -> bool)) +inf.0)
 #f)

(check-not-equal?
 (generate (typeof-e () (app (λ ((? x) bool) (if0 (var (? x)) true false)) false) bool) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () ((λ ((? y) (bool)) ((var (? y)) true)) true) (? t)) +inf.0)
 #f)

(check-not-equal?
 (generate (typeof-e ((x bool) ()) (var x) bool) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e ((x (bool-> bool)) ((x bool) ())) (var x) bool) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () (λ ((? x) bool) true) (bool -> (bool -> bool))) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () (λ ((? x) (bool -> bool)) (λ ((? x) bool) (app (var (? x)) true))) (? t)) +inf.0)
 #f)

(check-not-equal?
 (generates-well-typed? 5 100)
 #f)

(bound-measure 'depth)
(debug-out? #t)