#lang racket

(require "grammar.rkt"
         "../../predicates.rkt"
         redex/reduction-semantics)

(provide typeof
         to-type-form
         from-type-form)

; The typing rules in the paper, with two exceptions:
;
; 1. There are no type annotations on function parameters.
; I don't remember why I dropped them; adding them back seems easy.
;
; 2. Variables are represented as De Bruijin indices. There are two motivations
;    for this change:
;
;      a. Concrete names are hard to encode. I initially tried something like the
;         following, in which variables are still natural numbers but they no longer
;         count intervening binders.
;
;         [(bound (? x) (? Γ) (? τ))
;          (typeof (? Γ) (var (? x)) (? τ))
;          "var"]
;         [(typeof ([(? x) (? τ_1)] (? Γ)) (? e) (? τ_2))
;          (typeof (? Γ) (λ (? x) (? e)) (-> (? τ_1) (? τ_2)))
;          "abs"]
;
;         [(bound (? x) ([(? x) (? τ)] (? Γ)) (? τ))
;          "bound-found"]
;         [(neq (? x) (? y))
;          (bound (? x) (? Γ) (? τ))
;          (bound (? x) ([(? y) (? σ)] (? Γ)) (? τ))
;          "bound-continue"]
;
;         [(neq z (s (? x)))
;          "neq-sz"]
;         [(neq (s (? x)) z)
;          "neq-zs"]
;         [(neq (? x) (? y))
;          (neq (s (? x)) (s (? y)))
;          "neq-ss"]
;
;         The problem is the `neq' predicate, we can never conclude that two uninstantiated
;         variables are not equal. We'd like to make that conclusion, for example, to generate 
;         λx.λy.x at type α -> β -> α, but at the point that the generator tries to show
;         that x can be chosen to have type α, both x and y are totally uninstantiated, 
;         preventing it from skipping y's binding using the "bound-continue" rule.
;
;      b. It's nice that the generator doesn't bother, for example, to produce both λx.x and λy.y.

(define-predicate
  ; core forms
  ((typeof (? Γ) (unit) unit)
   "unit")
  ((bound (? x) (? Γ) (? τ))
   (typeof (? Γ) (var (? x)) (? τ))
   "var")
  ((typeof ((? τ_1) (? Γ)) (? e) (? τ_2))
   (typeof (? Γ) (λ (? e)) (-> (? τ_1) (? τ_2)))
   "abs")
  ((typeof (? Γ) (? e_1) (-> (? τ_2) (? τ)))
   (typeof (? Γ) (? e_2) (? τ_2))
   (typeof (? Γ) (app (? e_1) (? e_2)) (? τ))
   "app")
  ((typeof (? Γ) (? e_1) (? τ_1))
   (typeof (? Γ) (? e_2) (? τ_2))
   (typeof (? Γ) (pair (? e_1) (? e_2)) (pair (? τ_1) (? τ_2)))
   "pair")
  ((typeof (? Γ) (? e) (pair (? τ_1) (? τ_2)))
   (typeof (? Γ) (fst (? e)) (? τ_1))
   "fst")
  ((typeof (? Γ) (? e) (pair (? τ_1) (? τ_2)))
   (typeof (? Γ) (snd (? e)) (? τ_2))
   "snd")
  
  ; numbers
  ((typeof (? Γ) (num (? n)) num)
   "number")
  ((typeof (? Γ) + (-> num (-> num num)))
   "+")
  ((typeof (? Γ) * (-> num (-> num num)))
   "*")
  ((typeof (? Γ) / (-> num (-> num num)))
   "/")
  
  ; arrows
  ((typeof (? Γ) arr (-> (-> (? α) (? β))
                         (arr (? α) (? β))))
   "arr")
  ((typeof (? Γ) >>> (-> (arr (? α) (? β))
                         (-> (arr (? β) (? θ))
                             (arr (? α) (? θ)))))
   ">>>")
  ((typeof (? Γ) first (-> (arr (? α) (? β))
                           (arr (pair (? α) (? θ))
                                (pair (? β) (? θ)))))
   "first")
  ((typeof (? Γ) second (-> (arr (? α) (? β))
                            (arr (pair (? θ) (? α))
                                 (pair (? θ) (? β)))))
   "second")
  ((typeof (? Γ) loop (-> (arr (pair (? α) (? θ))
                               (pair (? β) (? θ)))
                          (arr (? α) (? β))))
   "loop")
  ((typeof (? Γ) init (-> (? α) (arr (? α) (? α))))
   "init"))

(define-predicate
  ((bound z ((? τ) (? Γ)) (? τ))
   "bound-eq")
  ((bound (? x) (? Γ) (? τ))
   (bound (s (? x)) ((? σ) (? Γ)) (? τ))
   "bound-neq"))

(define (to-type-form expr [env '()])
  (define (to-peano n)
    (for/fold ([p 'z]) ([_ (in-range n)])
      `(s ,p)))
  (define-metafunction CCA
    [(translate x_i (x_0 ... x_i x_i+1 ...))
     (var ,(to-peano (length (term (x_0 ...)))))]
    [(translate (λ (x) e) (x_0 ...))
     (λ (translate e (x x_0 ...)))]
    [(translate (e_1 e_2) (x_0 ...))
     (app (translate e_1 (x_0 ...))
          (translate e_2 (x_0 ...)))]
    [(translate () (x_0 ...))
     (unit)]
    [(translate number (x_0 ...))
     (num number)]
    [(translate (any ...) (x_0 ...))
     ((translate any (x_0 ...)) ...)]
    [(translate any (x_0 ...))
     any])
  (term (translate ,expr ,env)))

(define (from-type-form expr)
  (define from-peano
    (match-lambda
      ['z 0]
      [`(s ,n) (add1 (from-peano n))]))
  (let translate ([e expr] [d 0])
    (match e
      [`(var ,i)
       (string->symbol (format "x~s" (- d (from-peano i))))]
      [`(λ ,e)
       `(λ (,(string->symbol (format "x~s" (add1 d))))
          ,(translate e (add1 d)))]
      [`(app ,e1 ,e2)
       `(,(translate e1 d) ,(translate e2 d))]
      [`(unit) `()]
      [`(num ,n) n]
      [(? list?)
       (for/list ([x e])
         (translate x d))]
      [x x])))
