#lang racket

(require "../../predicates.rkt"
         rackunit)

(define-predicate
  [(not-in (? x) ())
   "not-in-empty"]
  [(not-in (? x) (? l))
   (neq (? x) (? y))
   (not-in (? x) ((? y) (? l)))
   "not-in-list"])

(check-equal?
 (generate (not-in a (a (b (c ())))) +inf.0)
 #f)

(check-equal?
 (generate (not-in d (a (b (c ())))) +inf.0)
 '())

(check-equal?
 (generate (not-in c (a (b (c ())))) +inf.0)
 #f)