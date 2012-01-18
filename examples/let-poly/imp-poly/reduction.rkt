#lang racket

(require "lang.rkt"
         redex/reduction-semantics)
(provide (all-defined-out))

;; TAG: syntax-states
(define-extended-language Λs/red Λs
  (Σ ([σ v] ...))
  (E hole
     (E e)
     (v E)
     (let (x E) e)
     (add1 E)
     (ref E)
     (! E)
     (E := e)
     (v := E)
     (seq E e))
  (v (λ x e)
     number
     (loc σ))
  (e .... (loc σ))
  (σ variable-not-otherwise-mentioned))

(define evaluate
  (let ([value (term-match/single
                Λs/red
                [(Σ v) (term v)]
                [any 'stuck])])
    (λ (e)
      (let loop ([p `(() ,e)])
        (match (apply-reduction-relation red p)
          [(list q) (loop q)]
          [(list) (value p)])))))

;; TAG: Λs-reduction
(define red
  (reduction-relation
   Λs/red
   (--> (Σ (in-hole E ((λ x e) v)))
        (Σ (in-hole E (subst x v e)))
        "app")
   (--> (Σ (in-hole E (let (x v) e)))
        (Σ (in-hole E (subst x v e)))
        "let")
   (--> (Σ (in-hole E (! (loc σ))))
        (Σ (in-hole E (lookup Σ σ)))
        "deref")
   (--> (Σ (in-hole E ((loc σ) := v)))
        ((update Σ σ v) (in-hole E 0))
        "update")
   (--> (Σ (in-hole E (ref v)))
        ((update Σ σ v) (in-hole E (loc σ)))
        (fresh σ)
        "ref")
   (--> (Σ (in-hole E (seq v e)))
        (Σ (in-hole E e))
        "seq")
   (--> (Σ (in-hole E (add1 number)))
        (Σ (in-hole E (succ number)))
        "add1")))

(define-metafunction Λs/red
  succ : number -> number
  [(succ number)
   ,(add1 (term number))])

(define-metafunction Λs/red
  lookup : Σ σ -> v
  [(lookup ([σ_0 v_0] ... [σ_i v_i] [σ_i+1 v_i+1] ...) σ_i) v_i])

(define-metafunction Λs/red
  update : Σ σ v -> Σ
  [(update ([σ_0 v_0] ... [σ_i v_i] [σ_i+1 v_i+1] ...) σ_i v_i′)
   ([σ_0 v_0] ... [σ_i v_i′] [σ_i+1 v_i+1] ...)]
  [(update ([σ_0 v_0] ...) σ_i v_i)
   ([σ_0 v_0] ... [σ_i v_i])])

(define-metafunction Λs/red
  subst : x any any -> any
  ;; 1. x_1 bound, so don't continue in body
  [(subst x_1 any_1 (λ x_1 any_2))
   (λ x_1 any_2)]
  [(subst x_1 any_1 (let (x_1 any_2) any_3))
   (let (x_1 (subst x_1 any_1 any_2)) any_3)]
  ;; 2. general purpose capture avoiding case
  [(subst x_1 any_1 (λ x_2 any_2))
   (λ x_new 
     (subst x_1 any_1
            (subst-vars (x_2 x_new) any_2)))
   (where x_new
          ,(variable-not-in
            (term (x_1 any_1 any_2)) 
            (term x_2)))]
  [(subst x_1 any_1 (let (x_2 any_2) any_3))
   (let (x_new (subst x_1 any_1 any_2))
     (subst x_1 any_1
            (subst-vars (x_2 x_new) any_3)))
   (where x_new
          ,(variable-not-in
            (term (x_1 any_1 any_3)) 
            (term x_2)))]
  ;; 3. replace x_1 with e_1
  [(subst x_1 any_1 x_1) any_1]
  ;; 4. x_1 and x_2 are different, so don't replace
  [(subst x_1 any_1 x_2) x_2]
  ;; the last cases cover all other expressions
  [(subst x_1 any_1 (any_2 ...))
   ((subst x_1 any_1 any_2) ...)]
  [(subst x_1 any_1 any_2) any_2])

(define-metafunction Λs/red
  subst-vars : (x any) ... any -> any
  [(subst-vars (x_1 any_1) x_1) any_1]
  [(subst-vars (x_1 any_1) (any_2 ...)) 
   ((subst-vars (x_1 any_1) any_2) ...)]
  [(subst-vars (x_1 any_1) any_2) any_2]
  [(subst-vars (x_1 any_1) (x_2 any_2) ... any_3) 
   (subst-vars (x_1 any_1) 
               (subst-vars (x_2 any_2) ... any_3))]
  [(subst-vars any) any])