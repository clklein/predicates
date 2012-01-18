#lang racket

(require "reduction-unspec.rkt" 
         redex)

(traces any-which-way-red
        (term (() (let (x (ref 0))
                    ((seq (x := 1)
                          (λ y (! x)))
                     (seq (x := 2)
                          3))))))