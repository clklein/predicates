#lang racket

; The language from “Causal Commutative Arrows and Their Optimization,”
; Liu et al. (ICFP '09)

(require redex/reduction-semantics)
(provide CCA)

(define-language CCA
  ((x y z) variable-not-otherwise-mentioned)
  (t unit num)
  ((α β θ) t
           (pair α β)
           (-> α β)
           (arr α β))
  ((e i j f g h)
   x
   (pair e e)
   (fst e)
   (snd e)
   (λ (x) e)
   (e e)
   ()
   
   k)
  (Γ ((x_0 α_0) ...))
  
  (k arr >>> first
     loop init
     
     real
     + * /))