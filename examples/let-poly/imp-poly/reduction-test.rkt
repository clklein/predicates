#lang racket

(require "reduction.rkt"
         redex/reduction-semantics)

(test-equal (evaluate (term (add1 0)))
            (term 1))
(test-equal (evaluate (term (add1 (add1 0))))
            (term 2))

(test-equal (evaluate (term (((λ x (λ y x)) (add1 0)) 0)))
            (term 1))

(test-equal (evaluate (term (let (x (add1 0)) (add1 x))))
            (term 2))

(test-equal (evaluate (term (let (x (ref 0))
                              (seq (ref 1)
                                   (seq (x := (add1 (! x)))
                                        (! x))))))
            (term 1))

(test-equal (evaluate 
             (term (let (r (ref (λ x x)))
                     (seq (r := (λ y (λ x x)))
                          (add1 ((! r) 2))))))
            (term stuck))

(test-equal (term (subst x 1 (let (x x) x)))
            (term (let (x 1) x)))
(test-equal (term (subst x y (let (y x) y)))
            (term (let (y1 y) y1)))

(test-results)