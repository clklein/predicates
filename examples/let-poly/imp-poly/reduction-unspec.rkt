#lang racket

(require "reduction.rkt"
         redex/reduction-semantics)
(provide any-which-way-red)

;; TAG: unspec-order
(define-extended-language
  any-which-way-Λs Λs/red
  (E .... (e E)))

;; TAG: unspec-order-red
(define any-which-way-red
  (extend-reduction-relation
   red any-which-way-Λs))