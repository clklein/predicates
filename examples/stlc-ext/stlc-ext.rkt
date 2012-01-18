#lang racket

(require "../../predicates.rkt"
         rackunit)

(provide one-term-preds
         preds-trace
         debug-out?
         gen-trace
         trace-trace
         bound-measure
         revisit-solved-goals?)

#|

e := x | i | (app e e) | (add1 e) | (inl e) | (inr e) | (pair e e)
  | (lamdba (x) e)
  | (fst e) | (snd e)
  | (case e
      [(inl x) => e]
      [(inr x) => e])

t := (unit) | (int) | (-> t t) | (* t t) | (+ t t)
 
|#

(define-predicate
  [(t-var (? Γ) (? x) (? t))
   (t-e (? Γ) (var (? x)) (? t))
   "t-e-var"]
  [(t-e (? Γ) () (unit))
   "t-e-unit"]
  [(t-e (? Γ) 0 (int))
   "t-e-0"]
  [(t-e (? Γ) add1 (-> (int) (int)))
   "t-e-add1"]
  [(t-e (? Γ) (? e1) (-> (? t2) (? t)))
   (t-e (? Γ) (? e2) (? t2))
   (t-e (? Γ) (app (? e1) (? e2)) (? t))
   "t-e-app"]
  [(t-e (((? x) (? tx)) (? Γ)) (? e) (? t))
   (t-e (? Γ) (lambda ((? x)) (? e)) (-> (? tx) (? t)))
   "t-e-lambda"]
  [(t-e (? Γ) (? e) (? te))
   (t-e (? Γ) (inl (? e)) (+ (? te) (? t_)))
   "t-e-inl"]
  [(t-e (? Γ) (? e) (? te))
   (t-e (? Γ) (inr (? e)) (+ (? t_) (? te)))
   "t-e-inr"]
  [(t-e (? Γ) (? e) (+ (? tl) (? tr)))
   (t-e (((? xl) (? tl)) (? Γ)) (? exl) (? t))
   (t-e (((? xr) (? tr)) (? Γ)) (? exr) (? t))
   (t-e (? Γ) (case (? e) [(inl (? xl)) => (? exl)] [(inr (? xr)) => (? exr)]) (? t))
   "t-e-case"]
  [(t-e (? Γ) (? el) (? tl))
   (t-e (? Γ) (? er) (? tr))
   (t-e (? Γ) (pair (? el) (? er)) (* (? tl) (? tr)))
   "t-e-pair"]
  [(t-e (? Γ) (? e) (* (? t) (? tr)))
   (t-e (? Γ) (fst (? e)) (? t))
   "t-e-fst"]
  [(t-e (? Γ) (? e) (* (? tl) (? t)))
   (t-e (? Γ) (snd (? e)) (? t))
   "t-e-snd"]
  [filtered-rules "t-e-var" "t-e-unit" "t-e-0" "t-e-add1"])

(define-predicate
  [(t-var (((? x) (? t)) (? Γ)) (? x) (? t))
   "this-x"]
  [(neq (? x) (? y))
   (t-var (? Γ) (? y) (? t))
   (t-var (((? x) (? tx)) (? Γ)) (? y) (? t))
   "another-x"]
  [always-order "this-x" "another-x"])

(define-syntax tt
  (syntax-rules ()
    [(tt term type)
     (check-not-equal? (generate (t-e () term type) +inf.0) #f)]))

(define-syntax tf
  (syntax-rules ()
    [(tt term)
     (check-equal? (generate (t-e () term (? t)) +inf.0) #f)]))

;; x
(tt (app (lambda (x) (var x)) 0) (int))

;; ()
(tt () (unit))

;; i
(tt 0 (int))

;; (e : T)
;;(tt (1 : (int)) (int))
;;(tf (1 : (-> (int) (int))))

;; (e e)
(tt (app add1 0) (int))
(tf (app add1 add1))
(tt (app (lambda (f) (app (var f) 0)) add1) (int))

;; lambda
#;(tt (lambda (x) (var x))
    (-> (? t) (? t)))

;; add1
(tt add1 (-> (int) (int)))

;; inl
(tt (inl 0) (+ (int) (? t)))

;; inr
(tt (inr 0) (+ (var A) (int)))

;; case
(tt (case (inl 0)
      [(inl x) => (app add1 (var x))]
      [(inr x) => (app add1 (app add1 (var x)))])
    (int))
(tt (case (inr 0)
      [(inl x) => (app add1 (var x))]
      [(inr x) => (app add1 (app add1 (var x)))])
    (int))
(tf (case (inl add1)
      [(inl x) => (app add1 (var x))]
      [(inr x) => (app add1 (app add1 (var x)))]))
(tf (case (inr add1)
      [(inl x) => (app add1 (var x))]
      [(inr x) => (app add1 (app add1 (var x)))]))
(tt (case (inr add1)
      [(inl x) => (var x)]
      [(inr x) => add1])
    (-> (int) (int)))
(tf (case (inr add1)
      [(inl x) => 0]
      [(inr x) => add1]))

;; pair
(tt (pair 0 0) (* (int) (int)))
(tt (pair 0 add1) (* (int) (-> (int) (int))))

;; fst
(tt (fst (pair 0 0)) (int))
(tt (fst (pair 0 add1)) (int))

;; snd
(tt (snd (pair 0 0)) (int))
(tt (snd (pair add1 0)) (int))

(bound-measure 'depth)
(revisit-solved-goals? #f)

(define preds-trace '())
(define trace-trace '())

(define shuffleinc 0)
(define (set-seed n) (set! shuffleinc n))
(define step 0)
(define (shufflez l)
  (when (debug-out?) (set! trace-trace (cons (if (empty? (gen-trace)) 'start (last (gen-trace))) trace-trace)))
  (set! preds-trace (cons `(,step ,shuffleinc ,(length l)) preds-trace))
  (random-seed shuffleinc)
  (set! shuffleinc (add1 shuffleinc))
  (set! step (add1 step))
  (shuffle l))

(current-permutations shufflez)

(define (one-term-preds seed)
  (set! step 0)
  (set! preds-trace '())
  (when (debug-out?) (set! trace-trace '()))
  (set-seed seed)
  (generate (t-e () (? e) (? t)) 5))