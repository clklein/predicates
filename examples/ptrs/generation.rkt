#lang racket

(require "typing.rkt"
         "../../main.rkt")

(define (random-expr)
  (parameterize ([bound-measure 'size]
                 [unbounded-predicates (list bop lv)]
                 [user-goal-solver 
                  (λ (predicate term constraints)
                    (displayln "Failure:")
                    (pretty-print (cons (object-name predicate) term))
                    #f)])7
    (generate (typeof-expr (? Γ) (? e) (? t)) 10)))