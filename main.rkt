#lang racket

(require "predicates.rkt")

(provide define-predicate
         term/c
         generate
         (struct-out lvar))

(provide/contract
 [bound-measure (parameter/c (one-of/c 'size 'depth))]
 [revisit-solved-goals? (parameter/c boolean?)])