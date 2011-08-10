#lang racket

(require "system-f.rkt"
         "../../main.rkt"
         rackunit)

(define-syntax-rule (type-passes t)
  (check-not-false (type-check t)))
(define-syntax-rule (type-fails t)
  (check-false (type-check t)))
(define-syntax-rule (type-check t)
  (generate t +inf.0))

;; similar types are also checked with the redex model
(parameterize ([debug-out? #f])
  (type-passes
   (typeof-e () () 
             (Λ α (λ (x (tvar α)) (var x))) 
             (∀ α (-> (tvar α) (tvar α)))))
  (type-passes
   (typeof-e () (α ()) 
             (λ (x (tvar α)) (var x)) 
             (-> (tvar α) (tvar α))))
  (type-fails
   (typeof-e () () 
             (Λ β (λ (x (tvar α)) (var x))) 
             (∀ α (-> (tvar α) (tvar α)))))
  (type-passes
   (typeof-e () () 
             (Λ α (Λ β (λ (x (tvar α)) (var x)))) 
             (∀ α (∀ β (-> (tvar α) (tvar α))))))
  (type-fails
   (typeof-e () () 
             (Λ α (Λ β (λ (x (tvar β)) (var x)))) 
             (∀ α (∀ β (-> (tvar α) (tvar α))))))
  (type-passes
   (typeof-e () () 
             (Λ α (Λ β (λ (x (tvar β)) (var x)))) 
             (∀ α (∀ β (-> (tvar β) (tvar β))))))
  (type-fails
   (typeof-e () () 
             (Λ α (λ (x (tvar β)) (var x))) 
             (∀ α (∀ β (-> (tvar β) (tvar β))))))
  (type-passes
   (typeof-e () () 
             (Λ α (t-app (Λ β (λ (x (tvar β)) (var x))) (tvar α)))
             (∀ α (-> (tvar α) (tvar α)))))
  (type-passes
   (typeof-e () () 
             (t-app (Λ α (t-app (Λ β (λ (x (tvar β)) (var x))) (tvar α))) ζ)
            (-> ζ ζ)))
  (type-fails
   (typeof-e () () 
             (t-app (t-app (Λ β (λ (x (tvar β)) (var x))) (tvar α)) ζ)
            (-> ζ ζ)))
  (type-passes
   (typeof-e () (β ())
             (t-app (Λ α (λ (x (tvar α)) (var x))) (tvar β))
             (-> (tvar β) (tvar β))))
  (type-fails
   (typeof-e () (β ())
             (t-app (Λ α (λ (x (-> (tvar α) (tvar α)) (var x))) (tvar β)))
             (-> (tvar β) (tvar β))))
  (type-passes
   (typeof-e () ()
             (Λ β (λ (f (-> (tvar β) (tvar β))) (λ (x (tvar β)) (app (var f) (app (var f) (var x))))))
             (∀ β (-> (-> (tvar β) (tvar β)) (-> (tvar β) (tvar β))))))
  (type-passes
   (typeof-e () ()
             (λ (x (∀ α (-> (tvar α) (tvar α)))) (app (t-app (var x) (∀ α (-> (tvar α) (tvar α)))) (var x)))
             (-> (∀ α (-> (tvar α) (tvar α))) (∀ α (-> (tvar α) (tvar α))))))
  (type-passes
   (typeof-e () ()
             (Λ α 
                (app (t-app (Λ β (λ (f (-> (tvar β) (tvar β))) (λ (x (tvar β)) (app (var f) (app (var f) (var x)))))) 
                            (-> (tvar α) (tvar α))) 
                     (t-app (Λ β (λ (f (-> (tvar β) (tvar β))) (λ (x (tvar β)) (app (var f) (app (var f) (var x)))))) 
                            (tvar α))))
             (∀ α (-> (-> (tvar α) (tvar α)) (-> (tvar α) (tvar α))))))
  (type-fails 
   (typeof-e  () ()
              (t-app (Λ α_0 (t-app (Λ α_0 (λ (x_1 (tvar α_0)) (var x_1))) t_2)) t_3)
              (-> (tvar α_0) (tvar α_0))))
  (type-passes ;; ?? is this type ok?
   (typeof-e () ()
             (Λ α_0 (λ (x_2 (-> (tvar α_0) (∀ α_3 (tvar α_0)))) (Λ α_3 (var x_2))))
             (∀ α_0 (-> (-> (tvar α_0) (∀ α_3 (tvar α_0))) (∀ α_3 (-> (tvar α_0) (∀ α_3 (tvar α_0))))))))
  )