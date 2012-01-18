#lang racket

(require "../../predicates.rkt"
         rackunit)

(provide (all-defined-out)
         generate)


#|

Γ;Σ+{Γ;Σ ⊢ x := ex} ⊢ e : τ 
-----------------------------------
Γ;Σ ⊢ (let ([(var x) ex]) in e : τ

Γ′;Σ′ ⊢ ex : τ
-----------------------------------
Γ;Σ+{Γ′;Σ′ ⊢ x := ex} ⊢ x : τ

|#
;; handle name clashes between the two contexts

(define-predicate
  [(typeof-e (((? x) (? t0)) (? env)) (? senv) (? e) (? t))
   (typeof-e (? env) (? senv) (λ (var (? x)) (? e)) (-> (? t0) (? t)))
   "e-lambda"]
  [(typeof-e (? env) (? senv) 0 num)
   "e-0"]
  [(typeof-e (? env) (? senv) (? e) num)
   (typeof-e (? env) (? senv) (add1 (? e)) num)
   "e-+1"]
  [(typeof-e (? env) (? senv) (? e0) (? t0))
   (typeof-e (? env) (? senv) (? e1) (-> (? t0) (? t)))
   (typeof-e (? env) (? senv) (app (? e1) (? e0)) (? t))
   "e-app"]
  [(var-type (? env) (? x) (? t))
   (typeof-e (? env) (? senv) (var (? x)) (? t))
   "e-var"]
  [(typeof-e (? env) (? senv) (? e) (? t))
   (typeof-e (? env) (? senv) (ref (? e)) (ref (? t)))
   "e-ref"]
  [(typeof-e (? env) (? senv) (? e) (ref (? t)))
   (typeof-e (? env) (? senv) (! (? e)) (? t))
   "e-deref"]
  [(typeof-e (? env) (? senv) (? e1) (? t1))
   (typeof-e (? env) (? senv) (? e2) (? t))
   (typeof-e (? env) (? senv) (seq (? e1) (? e2)) (? t))
   "e-seq"]
  [(not-in-e (? env) (? z))
   (typeof-e (? env) (((? env) (? senv) (? z) (? ex)) (? senv)) (? e) (? t))
   (typeof-e (? env) (? senv) (? ex) (? tex))
   (typeof-e (? env) (? senv) (let ([(var (? z)) (? ex)]) (? e)) (? t))
   "e-let"]
  [(subst-var (? senv) (? env0) (? senv0) (? z) (? ex))
   (typeof-e (? env0) (? senv0) (? ex) (? t))
   (typeof-e (? env) (? senv) (var (? z)) (? t))
   "e-subst"]
  [(typeof-e (? env) (? senv) (? e2) (? t))
   (typeof-e (? env) (? senv) (? e) (ref (? t)))
   (typeof-e (? env) (? senv) (s! (? e) (? e2)) num)
   "e-set"]
  [bounding-rules "e-0" "e-var" "e-ref" "e-lambda"])

(define-predicate
  [(subst-var (((? env) (? senv) (? x) (? ex)) (? senv)) (? env) (? senv) (? x) (? ex))
   "subst-this"]
  [(neq (? x) (? y))
   (subst-var (? senv0) (? env) (? senv) (? x) (? ex))
   (subst-var (((? env0) (? senv0) (? y) (? ex0)) (? senv0)) (? env) (? senv) (? x) (? ex))
   "subst-other"]
  [bounding-rules "subst-this" "subst-other"])

(define-predicate
  [(var-type (((? x) (? t)) (? env)) (? x) (? t))
   "found-var"]
  [(neq (? x) (? y))
   (var-type (? env) (? x) (? t))
   (var-type (((? y) (? t)) (? env)) (? x) (? t))
   "diff-var"]
  [bounding-rules "found-var" "diff-var"])

(define-predicate
  [(not-in-e () (? x))
   "not-in-empty-env"]
  [(neq (? x) (? y))
   (not-in-e (? env) (? y))
   (not-in-e (((? x) (? t)) (? env)) (? y))
   "not-in-this-env"]
  [bounding-rules "not-in-empty-env" "not-in-this-env"])


(check-equal?
 (generate (typeof-e () () (λ (var x) (var x)) num) +inf.0)
 #f)

(check-not-equal?
 (generate (typeof-e () () (λ (var x) (var x)) (-> num num)) +inf.0)
 #f)

(check-not-equal?
 (generate (typeof-e () () (app (λ (var (? x)) (add1 (var (? x)))) 0) num) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () () (app (λ (var (? y)) (app (var (? y)) 0)) 0) (? t)) +inf.0)
 #f)

(check-not-equal?
 (generate (typeof-e ((x num) ()) () (var x) num) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e ((x (-> num num)) ((x num) ())) () (var x) num) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () () (λ (var x) 0) (-> num (-> num num))) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () () (ref 0) (ref num)) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (! (ref 0)) num) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (app (λ (var x) (! (var x))) (ref 0)) num) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (! 0) (? t)) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () () (app (λ (var x) (! (var x))) 0) (? t)) +inf.0)
 #f)

(check-not-equal?
 (generate (typeof-e () () (app (λ (var (? x)) (ref (var (? x)))) (add1 0)) (ref num)) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () () (app (λ (var (? x)) (ref (var (? x)))) (add1 0)) num) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () () (seq (λ (var x) (var x)) 0) num) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (seq 0 (λ (var x) (add1 (var x)))) (-> num num)) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (λ (var x) (seq (app (var x) 7) (app (var x) (λ (var y) (var y))))) (? t)) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () () (s! (ref 0) (add1 0)) num) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (s! (ref 0) (λ (var x) 0)) num) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () () (s! (ref 0) (λ (var x) 0)) (-> num num)) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () () (let ([(var x) 0]) (var x)) num) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (let ([(var x) (λ (var y) (var y))]) (var x)) (-> num num)) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (let ([(var x) (λ (var y) (var y))]) 
                             (app (var x) 0)) 
                     num) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (let ([(var x) (λ (var y) (var y))])
                             (seq (app (var x) 0) 
                                  (app (var x) 0)))
                     num) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (let ([(var x) (λ (var y) (var y))])
                             (seq (app (var x) (var x)) 
                                  (app (var x) (add1 0))))
                     num) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (λ (var x) (add1 (app (! (var x)) 0))) (-> (ref (-> num num)) num)) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (λ (var x)
                             (seq (s! (var x) (λ (var z) 0))
                                  (add1 (app (! (var x)) 0))))
                     (-> (ref (-> num num)) num)) +inf.0)
 '())

;; ok
(check-equal?
 (generate (typeof-e () () (let ([(var x) (ref (λ (var y) (var y)))])
                             (seq (s! (var x) (λ (var z) 0))
                                  (add1 (app (! (var x)) 0))))
                     num) +inf.0)
 '())

;; not ok
(check-equal?
 (generate (typeof-e () () (let ([(var x) (ref (λ (var y) (var y)))])
                             (seq (s! (var x) (λ (var z) (λ (var a) (var a))))
                                  (add1 (app (! (var x)) 0))))
                     num) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (let ([(var x) (λ (var a) (var a))])
                             (let ([(var y) (λ (var b) (add1 (var b)))])
                               (app (var x) 0)))
                     num) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (λ (var x)
                             (let ([(var x) 0])
                               (var x)))
                     (? t)) +inf.0)
 #f)

(define (generates-well-typed? size tries)
  (for/and ([_ (in-range tries)])
    (match (generate (typeof-e () () (? e) (? t)) size)
      [`( (e ,e) (t ,t) )
       (unless (generate (typeof-e () () ,e ,t) +inf.0)
         (pretty-print e)
         (pretty-print t)
         false)])))

(define (fixup-vars exp)
  (let ([vars (hash)]
        [var-inc 0])
    (define (new-var sym)
      (let ([prefix (substring (symbol->string sym) 0 1)])
        (set! vars (hash-set vars sym (string->symbol (string-append prefix "_" (number->string var-inc)))))
        (set! var-inc (+ var-inc 1))
        (hash-ref vars sym)))
    (let recur ([e exp])
      (match e
        [(lvar x)
         (hash-ref vars x (lambda () (new-var x)))]
        [`(,es ...)
         (for/list ([e es]) (recur e))]
        [else e]))))

(define (gen size)
  (pretty-print (fixup-vars (generate (typeof-e () () (? e) (? t)) size))))

(bound-measure 'depth)

;; termination - the problem is substitution
;; rule ordering - don't want to apply this all the time, as it can definitely affect the terms
;; for example, in a let, all the time might get spent on the bound exp
;; ** if we're using size/depth bound?
;; "seeding" - provide an easy way to be more breadth first at the top of the tree somehow (i.e., don't apply the bound at all until depth x)
;; ** dude there is already a depth bound
;; unbounded predicate - should ignore bound instead of not incrementing it?
;; limit # of times rule can be applied in a subtree (i.e. let]
;; rewrite subst to make the two things in paralell??
;; variable renaming bug found ~1 hour :
;;;'(λ x_1 ((! (! (ref x_1))) := (let (x_1 (! x_1)) x_1)))
;;;#f
;;;'(λ x_1 ((! (! (ref x_1))) := (let (x_1 (! x_1)) x_1)))

;; after fixing subst:
;; 20 min:
;'(let (x_0 (ref (λ x_1 x_1)))
;   (seq
;    ((let (y_2 (! (seq 0 (ref x_0)))) x_0)
;     :=
;     (let (y_3 (λ x_4 x_4)) (λ y_5 x_0)))
;    (((seq (let (y_6 0) 0) (! x_0)) (λ y_7 (add1 0)))
;     ((let (y_8 (! (ref (ref x_0)))) (seq 0 (ref x_0)))
;      :=
;      (seq (λ y_9 0) x_0)))))
;
;'(let (x_0 (ref (λ x_1 x_1)))
;   (seq
;    ((let (y_2 (! (seq 0 (ref x_0)))) x_0)
;     :=
;     (let (y_3 (λ x_4 x_4)) (λ y_5 x_0)))
;    (((seq (let (y_6 0) 0) (! x_0)) (λ y_7 (add1 0)))
;     ((let (y_8 (! (ref (ref x_0)))) (seq 0 (ref x_0)))
;      :=
;      (seq (λ y_9 0) x_0)))))
;
;'(let (x (ref (λ z z)))
;   (seq
;    (x := (λ y x))
;    (((! x) (λ y 0))
;     ((ref x) := x))))

