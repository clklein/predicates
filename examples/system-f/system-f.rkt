#lang racket

(require "../../predicates.rkt"
         "f-redex.rkt"
         rackunit
         redex)

(provide (all-defined-out))

;; -- requires that rule ordering is not randomized --

;; e ::= (λ (x t) e) | (app e e) | (var x) | (Λ α e) | (t-app e t)
;; t ::= (tvar α) | (-> t t) | (∀ α t)
;; env ::= () | ((x t) env)
;; tenv ::= () | (α env)

;; there were some problems with things like ∀ getting
;; instantiated in a logic variable, which were solved by changing
;; (t -> t) to (-> t t) so -> clashed directly with ∀
;; something to think about for the future though -
;; probably shouldn't let logic values be instantiated
;; to symbols that have meaningful program syntax

(define-predicate
  [(typeof-e (? env) (? tenv) (? e2) (? t1))
   (typeof-e (? env) (? tenv) (? e1) (-> (? t1) (? t2)))
   (typeof-e (? env) (? tenv) (app (? e1) (? e2)) (? t2))
   "typeof-application"]
  [(typeof-var (? env) (? x) (? t))
   (typeof-e (? env) (? tenv) (var (? x)) (? t))
   "typeof-var"]
  [(typeof-e (((? x) (? t1)) (? env)) (? tenv) (? e) (? t2))
   (typeof-e (? env) (? tenv) (λ ((? x) (? t1)) (? e)) (-> (? t1) (? t2)))
   "typeof-abstraction"] 
  [(not-in (? α) (? tenv))
   (typeof-e (? env) ((? α) (? tenv)) (? e) (? t))
   (typeof-e (? env) (? tenv) (Λ (? α) (? e)) (∀ (? α) (? t)))
   "typeof-type-abstraction"]
  [(typeof-e (? env) (? tenv) (? e) (∀ (? α) (? t1)))
   (substitute-type (? t) (? α) (? t1) (? t2))
   (typeof-e (? env) (? tenv) (t-app (? e) (? t)) (? t2))
   "typeof-type-appplication"]
  [bounding-rules "typeof-var" "typeof-abstraction" "typeof-type-abstraction" "typeof-application"])

;; this predicate needs to *always* be ordered
;; because it's bad if "subst-not-alpha" comes before
;; "subst-func" or "subst-forall" 
;; requires some changes to predicates.rkt
;; note: (neq (? t1) (-> (? t2) (? t3))) won't work 
;; because t2 and t3 just get thrown away
(define-predicate
  [(substitute-type (? t) (? α) (tvar (? α)) (? t))
   "subst-alpha"]
  [(neq (tvar (? α)) (? t1))
   (substitute-type (? t) (? α) (? t1) (? t1))
   "subst-not-alpha"]
  [(substitute-type (? t) (? α) (? t2) (? t2f))
   (substitute-type (? t) (? α) (? t1) (? t1f))
   (substitute-type (? t) (? α) (-> (? t1) (? t2)) (-> (? t1f) (? t2f)))
   "subst-func"]
  [(neq (? α) (? α1))
   (substitute-type (? t) (? α) (? t) (? tf))
   (substitute-type (? t) (? α) (∀ (? α1) (? t)) (∀ (? α1) (? tf)))
   "subst-forall"]
  [always-order "subst-alpha" "subst-forall" "subst-func" "subst-not-alpha"])

(define-predicate
  [(typeof-var (((? x) (? t)) (? env)) (? x) (? t))
   "found-var"]
  [(typeof-var (? env) (? y) (? t))
   (neq (? x) (? y))
   (typeof-var (((? x) (? t1)) (? env)) (? y) (? t))
   "keep-looking"]
  [bounding-rules "found-var" "keep-looking"])

(define-predicate
  [(typeof-tvar ((? α) (? tenv)) (? α))
   "found-tvar"]
  [(typeof-tvar (? tenv) (? α))
   (typeof-tvar ((? αt) (? tenv)) (? α))
   "another-tvar"]
  [bounding-rules "found-tvar" "another-tvar"])

(define-predicate
  [(not-in (? α) ())
   "not-in-empty"]
  [(neq (? α) (? β))
   (not-in (? α) (? l))
   (not-in (? α) ((? β) (? l)))
   "not-in-list"]
  [bounding-rules "not-in-empty" "not-in-list"])


;; stuff to cleanup the format and check with the redex model:

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

(define (to-redex-format exp)
  (to-redex (fixup-vars exp)))

(define (to-redex exp)
  (match exp
    [`(t-app ,e ,t)
     `(,(to-redex e) [,(to-redex t)])]
    [`(app ,e1 ,e2)
     `(,(to-redex e1) ,(to-redex e2))]
    [`(tvar ,α)
     α]
    [`(var ,x)
     x]
    [`(,es ...)
     (for/list ([e es]) (to-redex e))]
    [else exp]))

(define (redex-tc e t)
  (printf "tc: ~a ~a\n" e t)
  (test-equal (term (tc ,e () ())) (term ,t)))

(define (gen-and-check)
  (define res (generate (typeof-e () () (Λ δ (? e)) (? t)) 10))
  (define res-rdx (to-redex-format res))
  (printf "~a\n" res)
  (match res-rdx
    [`((e ,exp) (t ,type))
     (redex-tc `(Λ δ ,exp) type)]
    [`((t ,type) (e ,exp))
     (redex-tc `(Λ δ ,exp) type)]))

