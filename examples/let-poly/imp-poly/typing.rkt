#lang racket

(require "lang.rkt"
         redex/reduction-semantics)

(provide typeof
         unify
         instantiate
         TV
         subst-constraints
         subst-type)

(define-extended-language Λs/ty Λs
  (t num
     x
     (t -> t)
     (ref t))
  (c [t = t])
  (C (c ...))
  (σ ([x = t] ...))
  (X (x ...))
  (s (∀ (x ...) t))
  (Γ ([x s] ...)))

(define-metafunction Λs/ty
  typeof : Γ e -> s or #f
  [(typeof Γ e)
   (generalize Γ t σ)
   (where (t C X) (constrained-type Γ e ()))
   (where σ (unify C))]
  [(typeof Γ e) #f])

(define-metafunction Λs/ty
  constrained-type : Γ e X -> (t C X) or #f
  [(constrained-type Γ (λ x e) X)
   ((t_d -> t) C X_**)
   (where (t_d X_*) (fresh-TV X))
   (where (t C X_**) (constrained-type (extend Γ x (∀ () t_d)) e X_*))]
  [(constrained-type Γ (e_1 e_2) X)
   (t_r (union-constraints C_1 C_2 ([t_1 = (t_2 -> t_r)])) X_***)
   (where (t_1 C_1 X_*) (constrained-type Γ e_1 X))
   (where (t_2 C_2 X_**) (constrained-type Γ e_2 X_*))
   (where (t_r X_***) (fresh-TV X_**))]
  [(constrained-type Γ (let (x_1 e_1) e_2) X)
   (t_2 (union-constraints C_1 C_2) X_**)
   (where (t_1 C_1 X_*) (constrained-type Γ e_1 X))
   (where σ (unify C_1))
   (where s_1 (generalize Γ t_1 σ))
   (where (t_2 C_2 X_**) (constrained-type (extend Γ x_1 s_1) e_2 X_*))]
  [(constrained-type Γ x X)
   (t_i () X_*)
   (where (∀ (x_0 ...) t) (lookup Γ x))
   (where (t_i X_*) (instantiate t (x_0 ...) X))]
  
  [(constrained-type Γ (ref e) X)
   ((ref t) C X_*)
   (where (t C X_*) (constrained-type Γ e X))]
  [(constrained-type Γ (! e) X)
   (t (union-constraints ([t_e = (ref t)]) C) X_**)
   (where (t_e C X_*) (constrained-type Γ e X))
   (where (t X_**) (fresh-TV X_*))]
  [(constrained-type Γ (e_1 := e_2) X)
   (num (union-constraints ([t_1 = (ref t_2)]) C_1 C_2) X_**)
   (where (t_1 C_1 X_*) (constrained-type Γ e_1 X))
   (where (t_2 C_2 X_**) (constrained-type Γ e_2 X_*))]
  [(constrained-type Γ (seq e_1 e_2) X)
   (t_2 (union-constraints C_1 C_2) X_**)
   (where (t_1 C_1 X_*) (constrained-type Γ e_1 X))
   (where (t_2 C_2 X_**) (constrained-type Γ e_2 X_*))]
  
  [(constrained-type Γ (add1 e) X)
   (num (union-constraints ([t = num]) C) X_*)
   (where (t C X_*) (constrained-type Γ e X))]
  [(constrained-type Γ number X)
   (num () X)]
  
  ; a `let' RHS within e is locally inconsistent
  [(constrained-type Γ e X) #f])

(define-metafunction Λs/ty
  generalize : Γ t σ -> s
  [(generalize ([x_0 (∀ X_0 t_0)] ...) t σ)
   (∀ ,(remove* (apply append (term ((TV t_0*) ...)))
                (term (TV t_*)))
      t_*)
   (where t_* (apply-subst σ t))
   ; σ won't unify TVs bound in the t_i since those TVs
   ; turn into fresh instances while collecting the
   ; constraints that lead to σ
   (where (t_0* ...) ((apply-subst σ t_0) ...))])

(define-metafunction Λs/ty
  instantiate : t (x ...) X -> (t X)
  ; expects TV(t) ⊆ X
  [(instantiate t () X) (t X)]
  [(instantiate t (x_0 x_1 ...) X)
   (instantiate (subst-type t x_0 t_f) (x_1 ...) X_*)
   (where (t_f X_*) (fresh-TV X))])

(define-metafunction Λs/ty
  lookup : Γ x -> s
  [(lookup ([x_0 s_0] ... [x_i s_i] [x_i+1 s_i+1] ...) x_i)
   s_i
   (side-condition (not (member (term x_i) (term (x_0 ...)))))])

(define-metafunction Λs/ty
  extend : Γ x s -> Γ
  [(extend ([x_1 s_1] ...) x_0 s_0)
   ([x_0 s_0] [x_1 s_1] ...)])

(define-metafunction Λs/ty
  unify : C -> σ or #f
  [(unify ()) ()]
  [(unify ([t = t] c ...))
   (unify (c ...))]
  [(unify ([t = x] c ...))
   (unify-var x t (c ...))]
  [(unify ([x = t] c ...))
   (unify-var x t (c ...))]
  [(unify ([(t_1 -> t_2) = (t_3 -> t_4)] c ...))
   (unify ([t_1 = t_3] [t_2 = t_4] c ...))]
  [(unify ([(ref t_1) = (ref t_2)] c ...))
   (unify ([t_1 = t_2] c ...))]
  [(unify (c ...)) #f])

(define-metafunction Λs/ty
  unify-var : x t C -> σ or #f
  [(unify-var x t (c ...))
   ([x = t] [x_0 = t_0] ...)
   (where ([x_0 = t_0] ...) (unify (subst-constraints (c ...) x t)))
   (side-condition (not (member (term x) (term (TV t)))))]
  [(unify-var x t C) #f])

(define-metafunction Λs/ty
  TV : t -> (x ...)
  [(TV num) ()]
  [(TV bool) ()]
  [(TV x) (x)]
  [(TV (t_1 -> t_2))
   ,(remove-duplicates (term (x_0 ... x_i ...)))
   (where (x_0 ...) (TV t_1))
   (where (x_i ...) (TV t_2))]
  [(TV (ref t)) (TV t)])

(define-metafunction Λs/ty
  union-constraints : C ... -> C
  [(union-constraints C ...)
   ,(apply append (term (C ...)))])

(define-metafunction Λs/ty
  subst-constraints : C x t -> C
  [(subst-constraints ([t_1 = t_2] ...) x t)
   ([(subst-type t_1 x t) = (subst-type t_2 x t)] ...)])

(define-metafunction Λs/ty
  subst-type : t x t -> t
  [(subst-type num x t) num]
  [(subst-type bool x t) bool]
  [(subst-type x x t) t]
  [(subst-type x_1 x_2 t) x_1]
  [(subst-type (t_1 -> t_2) x t)
   ((subst-type t_1 x t) -> (subst-type t_2 x t))]
  [(subst-type (ref t_1) x t)
   (ref (subst-type t_1 x t))])

(define-metafunction Λs/ty
  apply-subst : σ t -> t
  [(apply-subst () t) t]
  [(apply-subst ([x_0 = t_0] [x_1 = t_1] ...) t)
   (apply-subst ([x_1 = t_1] ...) (subst-type t x_0 t_0))])

(define-metafunction Λs/ty
  fresh-TV : X -> (x X)
  [(fresh-TV (x_0 ...))
   (x_i (x_0 ... x_i))
   (where x_i ,(variable-not-in (term (x_0 ...)) 'x1))])