#lang racket

(require redex)

(provide (all-defined-out))

(define-language F
  (e (e e) (e [t]) x v)
  (v (λ (x t) e) (Λ α e))
  (t (-> t t) (∀ α t) α)
  (E (E e) (v E) (E [t]) hole)
  (x variable-not-otherwise-mentioned)
  (α variable-not-otherwise-mentioned))

(define red
  (reduction-relation
   F
   (--> (in-hole E ((λ (x t) e) v))
        (in-hole E (subst-x x v e))
        "βv")
   (--> (in-hole E ((Λ α e) [t]))
        (in-hole E (subst-α α t e)))))


(define-metafunction F
  subst-x : x any any -> any
  ;; 1. x_1 bound, so don't continue in λ body
  [(subst-x x_1 any_1 (λ (x_1 t_1) any_2))
   (λ (x_1 t_1) any_2)]
  ;; 2. general purpose capture avoiding case
  [(subst-x x_1 any_1 (λ (x_2 t_2) any_2))
   (λ (x_new t_2) 
     (subst-x x_1 any_1
              (subst-var x_2 x_new any_2)))
   (where x_new ,(variable-not-in
                  (term (x_1 any_1 any_2)) 
                  (term x_2)))]
  ;; 3. replace x_1 with e_1
  [(subst-x x_1 any_1 x_1) any_1]
  ;; 4. x_1 and x_2 are different, so don't replace
  [(subst-x x_1 any_1 x_2) x_2]
  ;; the last cases cover all other expressions
  [(subst-x x_1 any_1 (any_2 ...))
   ((subst-x x_1 any_1 any_2) ...)]
  [(subst-x x_1 any_1 any_2) any_2])

(define-metafunction F
  subst-var : x any any -> any
  [(subst-var x_1 any_1 x_1) any_1]
  [(subst-var x_1 any_1 (any_2 ...)) 
   ((subst-var x_1 any_1 any_2) ...)]
  [(subst-var x_1 any_1 any_2) any_2]
  [(subst-var any) any])


;; just like x-substitution, except with Λ and α
(define-metafunction F
  subst-α : α any any -> any
  [(subst-α α_1 any_1 (Λ α_1 any_2))
   (Λ α_1 any_2)]
  [(subst-α α_1 any_1 (Λ α_2 any_2))
   (Λ α_new 
      (subst-α α_1 any_1
               (subst-var-α α_2 α_new any_2)))
   (where α_new ,(variable-not-in
                  (term (α_1 any_1 any_2)) 
                  (term α_2)))]
  [(subst-α α_1 any_1 α_1) any_1]
  [(subst-α α_1 any_1 α_2) α_2]
  [(subst-α α_1 any_1 (any_2 ...))
   ((subst-α α_1 any_1 any_2) ...)]
  [(subst-α α_1 any_1 any_2) any_2])

(define-metafunction F
  subst-var-α : α any any -> any
  [(subst-var-α α_1 any_1 α_1) any_1]
  [(subst-var-α α_1 any_1 (any_2 ...)) 
   ((subst-var-α α_1 any_1 any_2) ...)]
  [(subst-var-α α_1 any_1 any_2) any_2]
  [(subst-var-α any) any])

;; e env tenv -> t or #f
(define-metafunction F
  tc : e ((x t) ...) (α ...) -> t or #f
  [(tc x_1 ((x_2 t_2) ... (x_1 t_1) (x_3 t_3) ...) (α_1 ...))
   t_1
   (side-condition (not (member (term x_1) (term (x_2 ...)))))]
  [(tc (e_1 e_2) ((x t) ...) (α ...))
   t_3
   (where (-> t_2 t_3) (tc e_1 ((x t) ...) (α ...)))
   (where t_2 (tc e_2 ((x t) ...) (α ...)))]
  [(tc (λ (x_1 t_1) e) ((x_2 t_2) ...) (α ...))
   (-> t_1 t)
   (where t (tc e ((x_1 t_1) (x_2 t_2) ...) (α ...)))]
  [(tc (Λ α_1 e_1) ((x t) ...) (α_2 ...))
   (∀ α_new t_1)
   (where α_new ,(variable-not-in (term (α_2 ...))
                                  (term α_1)))
   (where e_new (subst-var-α α_new α_1 e_1))
   (where t_1 (tc e_new ((x t) ...) (α_new α_2 ...)))]
  [(tc (e_1 [t_1]) ((x t) ...) (α ...))
   (subst-α α_1 t_1 t_2)
   (where (∀ α_1 t_2) (tc e_1 ((x t) ...) (α ...)))]
  [(tc e ((x t) ...) (α ...)) 
   #f])

;; a few examples from Pierce
(test-equal (term (tc (Λ α (λ (x α) x)) () ()))
            (term (∀ α (-> α α))))
(test-equal (term (tc ((Λ α (λ (x α) x)) [β]) () ()))
            (term (-> β β)))
(test-equal (term (tc (Λ β (λ (f (-> β β)) (λ (x β) (f (f x))))) () ()))
            (term (∀ β (-> (-> β β) (-> β β)))))
(test-equal (term (tc (λ (x (∀ α (-> α α))) ((x [(∀ α (-> α α))]) x)) () ()))
            (term (-> (∀ α (-> α α)) (∀ α (-> α α)))))
(test-equal (term (tc (Λ α 
                         (((Λ β (λ (f (-> β β)) (λ (x β) (f (f x))))) 
                           [(-> α α)]) 
                          ((Λ β (λ (f (-> β β)) (λ (x β) (f (f x))))) 
                           [α]))) 
                      () ()))
            (term (∀ α (-> (-> α α) (-> α α)))))


(test-equal (term (tc (((Λ α (λ (x α) x)) [(-> β β)]) ((Λ α (λ (x α) x)) [β])) () ()))
            (term (-> β β)))
(test-->> red 
          (term (((Λ α (λ (x α) x)) [(-> β β)]) ((Λ α (λ (x α) x)) [β])))
          (term (λ (x β) x)))
;; the Λ abstraction part of the following is typed above:
(test-->> red 
          (term ((Λ α 
                    (((Λ β (λ (f (-> β β)) (λ (x β) (f (f x))))) 
                      [(-> α α)]) 
                     ((Λ β (λ (f (-> β β)) (λ (x β) (f (f x))))) 
                      [α]))) [δ]))
          (term (λ (x1 (-> δ δ))
                  ((λ (f (-> δ δ))
                     (λ (x δ) (f (f x))))
                   ((λ (f (-> δ δ))
                      (λ (x δ) (f (f x))))
                    x1)))))







   
   
   
   