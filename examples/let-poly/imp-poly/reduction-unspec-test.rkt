#lang racket

(require "reduction-unspec.rkt"
         redex/reduction-semantics)

(test-->> any-which-way-red
          (term (() (let (x (ref 0))
                      ((seq (x := 1)
                            (λ y (! x)))
                       (seq (x := 2)
                            3)))))
          (term (([σ 1]) 1))
          (term (([σ 2]) 2)))

(test-results)