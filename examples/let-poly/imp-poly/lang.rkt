#lang racket

(require redex/reduction-semantics)
(provide Λs)

;; TAG: syntax-exprs
(define-language Λs
  (e (λ x e)
     (e e)
     (let (x e) e)
     x
     (ref e)
     (! e)
     (e := e)
     (seq e e)
     (add1 e)
     number)
  (x variable-not-otherwise-mentioned))