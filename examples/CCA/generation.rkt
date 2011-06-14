#lang racket

(require "grammar.rkt"
         "typing.rkt"
         "../../predicates.rkt"
         redex/reduction-semantics)

; Prints some random arrow-typed expressions. For example,
;
; $ racket -tm- generation.rkt --size --unbounded-variable-derivations --solve-base-cases 10 5
;
; prints 10 expressions, each having typing derivations with size less than 5
;
; The terms that come out of `generate' can contain holes, in the form of `lvars'. 
; For this particular type system, I don't think `generate' will produce such terms, 
; but just in case, `random-arrow' uses Redex's built-in syntactic-constraints-only
; generator `generate-term' to fill in the holes. 
;
; It also replacing De Bruijn indices with concrete names to make the results prettier.

(provide random-arrow
         main
         bound-measure
         user-goal-solver
         generate-base)

(define (main . args)
  (define seed (add1 (random (sub1 (expt 2 31)))))
  
  (command-line
   #:argv args
   
   #:once-any
   ["--depth"  
    "Bounds the depth of the typing derivations of random expressions"
    (bound-measure 'depth)]
   ["--size"  
    "Bounds the size of the typing derivations of random expressions"
    (bound-measure 'size)]
   
   #:once-any
   ["--unbounded-variable-derivations"
    "Excludes the depth/size of `bound' derivations"
    (unbounded-predicates (list bound))]
   
   #:once-each
   ["--no-revisit-solved"  
    "Disables backtracking to find different solutions to solved goals"
    (revisit-solved-goals? #f)]
   ["--solve-base-cases"
    "Chooses a simple solution when the depth/size bound is zero"
    (user-goal-solver generate-base)]
   ["--seed"
    n
    "Seed with PRG with n"
    (set! seed (string->number n))]
   
   #:args (number-programs derivation-bound)
   (printf "Random seed: ~s\n" seed)
   (random-seed seed)
   (sample-arrows (string->number number-programs) 
                  (string->number derivation-bound))))

(define (random-expr-instance expr [env (make-hash)])
  (define (random-constant)
    (generate-term CCA k 1))
  (define (random-number)
    (generate-term CCA real (random 3)))
  (let recur ([e expr])
    (match e
      [`(num ,(lvar x))
       (instantiate x random-number env)]
      [(lvar x)
       (instantiate x random-constant env)]
      [(? list?)
       (map recur e)]
      [_ e])))

(define (instantiate var make env)
  (match (hash-ref env var #f)
    [#f (define i (make))
        (hash-set! env var i)
        i]
    [i i]))

(define (random-arrow size)
  (cond [(generate (typeof • (? e) (arr (? α) (? β))) size)
         => (compose from-type-form
                     random-expr-instance
                     second
                     (curry assoc 'e))]
        [else (error 'random-expression "failure at size ~s" size)]))

(define (sample-arrows samples size)
  (time
   (for ([_ (in-range samples)])
     (pretty-display (random-arrow size)))))

(define (generate-base pred term csts)
  (let ([env (cstrs-eqs csts)])
    (cond [(equal? pred typeof)
           (match term
             [(list Γ (lvar x) τ)
              (let-values ([(e env’) (generate-base-type Γ τ env)])
                (struct-copy cstrs csts [eqs (hash-set env’ x e)]))])]
          [else #f])))


(define (generate-base-type Γ τ env)
  (match τ
    [(lvar x)
     (values `(num ,(lvar (gensym 'n))) (hash-set env x 'num))]
    ['num
     (values `(num ,(lvar (gensym 'n))) env)]
    ['unit
     (values '(unit) env)]
    [`(pair ,α ,β)
     (let*-values ([(a env’) (generate-base-type Γ α env)]
                   [(b env’’) (generate-base-type Γ β env)])
       (values `(pair ,a ,b) env’’))]
    [`(-> ,α ,β)
     (let-values ([(b env’) (generate-base-type Γ β env)])
       (values `(λ ,b) env’))]
    [`(arr ,α ,β)
     (let-values ([(f env’) (generate-base-type Γ `(-> ,α ,β) env)])
       (values `(arr ,f) env’))]))