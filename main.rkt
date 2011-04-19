#lang racket

(require "predicates.rkt")

(provide define-predicate
         term/c
         generate
         (struct-out lvar))

(provide/contract
 [bound-measure (parameter/c (one-of/c 'size 'depth))]
 [unbounded-predicates (parameter/c (listof procedure?))]
 [user-goal-solver (parameter/c (-> procedure? term/c (hash/c symbol? term/c)
                                    (or/c #f (hash/c symbol? term/c))))]
 [revisit-solved-goals? (parameter/c boolean?)]
 [current-permutations (parameter/c (-> list? list?))])