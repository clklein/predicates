#lang racket

(require "predicates.rkt")

(provide define-predicate
         term/c
         generate
         (struct-out lvar))

(provide/contract
 [bound-measure (parameter/c (one-of/c 'size 'depth))]
 [unbounded-predicates (parameter/c (listof procedure?))]
 [user-goal-solver (parameter/c (-> procedure? term/c (struct/c cstrs (hash/c symbol? term/c) list?)
                                    (or/c #f (struct/c cstrs (hash/c symbol? term/c) list?))))]
 [revisit-solved-goals? (parameter/c boolean?)]
 [current-permutations (parameter/c (-> list? list?))]
 [debug-out? (parameter/c boolean?)])