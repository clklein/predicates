#lang racket

(require "../../predicates.rkt"
         rackunit)

(provide (all-defined-out)
         bound-measure
         generate)

#|

modulo names tracking, judgments look like:

Γ;Σ+{Γ;Σ ⊢ x := ex} ⊢ e : τ 
-----------------------------------
Γ;Σ ⊢ (let ([(var x) ex]) in e : τ

Γ′;Σ′ ⊢ ex : τ
-----------------------------------
Γ;Σ+{Γ′;Σ′ ⊢ x := ex} ⊢ x : τ

Σ - "substitution context"
(the above are the only two that use Σ)

|#
;; handle name clashes between the two contexts

(define-predicate
  [(not-in (? names) (? x))
   (typeof-e (((? x) (? t0)) (? env)) (? senv) (? e) (? t) ((? x) (? names)))
   (typeof-e (? env) (? senv) (λ (var (? x)) (? e)) (-> (? t0) (? t)) (? names)) 
   "e-lambda"]
  [(typeof-e (? env) (? senv) 0 num (? names))
   "e-0"]
  [(typeof-e (? env) (? senv) (? e) num (? names))
   (typeof-e (? env) (? senv) (add1 (? e)) num (? names))
   "e-+1"]
  [(typeof-e (? env) (? senv) (? e0) (? t0) (? names))
   (typeof-e (? env) (? senv) (? e1) (-> (? t0) (? t)) (? names))
   (typeof-e (? env) (? senv) (app (? e1) (? e0)) (? t) (? names))
   "e-app"]
  [(var-type (? env) (? x) (? t))
   (typeof-e (? env) (? senv) (var (? x)) (? t) (? names))
   "e-var"]
  [(typeof-e (? env) (? senv) (? e) (? t) (? names))
   (typeof-e (? env) (? senv) (ref (? e)) (ref (? t)) (? names))
   "e-ref"]
  [(typeof-e (? env) (? senv) (? e) (ref (? t)) (? names))
   (typeof-e (? env) (? senv) (! (? e)) (? t) (? names))
   "e-deref"]
  [(typeof-e (? env) (? senv) (? e1) (? t1) (? names))
   (typeof-e (? env) (? senv) (? e2) (? t) (? names))
   (typeof-e (? env) (? senv) (seq (? e1) (? e2)) (? t) (? names))
   "e-seq"]
  [(not-in (? names) (? z))
   (typeof-e (? env) (((? env) (? senv) (? z) (? ex)) (? senv)) (? e) (? t) ((? x) ((? z) (? names)))) ;; doing this first leads to less backtracking?
   (typeof-e (? env) (? senv) (? ex) (? tex) ((? x) ((? z) (? names))))
   (typeof-e (? env) (? senv) (let ([(var (? z)) (? ex)]) (? e)) (? t) (? names))
   "e-let"]
  [(subst-var (? senv) (? env0) (? senv0) (? z) (? ex))
   (typeof-e (? env0) (? senv0) (? ex) (? t) (? names))
   (typeof-e (? env) (? senv) (var (? z)) (? t) (? names))
   "e-subst"]
  [(typeof-e (? env) (? senv) (? e2) (? t) (? names))
   (typeof-e (? env) (? senv) (? e) (ref (? t)) (? names))
   (typeof-e (? env) (? senv) (s! (? e) (? e2)) num (? names))
   "e-set"]
  [bounding-rules "e-0" "e-+1" "e-var" "e-subst" "e-ref" "e-lambda" "e-deref" "e-seq" "e-set" "e-let"])

(define-predicate
  [(not-in () (? x))
   "not-in-empty"]
  [(neq (? x) (? y))
   (not-in (? names) (? x))
   (not-in ((? y) (? names)) (? x))
   "not-in-car"]
  [bounding-rules "not-in-car" "not-in-empty"])


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


(check-equal?
 (generate (typeof-e () () (λ (var x) (var x)) num ()) +inf.0)
 #f)

(check-not-equal?
 (generate (typeof-e () () (λ (var x) (var x)) (-> num num) ()) +inf.0)
 #f)

(check-not-equal?
 (generate (typeof-e () () (app (λ (var (? x)) (add1 (var (? x)))) 0) num ()) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () () (app (λ (var (? y)) (app (var (? y)) 0)) 0) (? t) ()) +inf.0)
 #f)

(check-not-equal?
 (generate (typeof-e ((x num) ()) () (var x) num ()) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e ((x (-> num num)) ((x num) ())) () (var x) num ()) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () () (λ (var x) 0) (-> num (-> num num)) ()) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () () (ref 0) (ref num) ()) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (! (ref 0)) num ()) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (app (λ (var x) (! (var x))) (ref 0)) num ()) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (! 0) (? t) ()) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () () (app (λ (var x) (! (var x))) 0) (? t) ()) +inf.0)
 #f)

(check-not-equal?
 (generate (typeof-e () () (app (λ (var (? x)) (ref (var (? x)))) (add1 0)) (ref num) ()) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () () (app (λ (var (? x)) (ref (var (? x)))) (add1 0)) num ()) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () () (seq (λ (var x) (var x)) 0) num ()) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (seq 0 (λ (var x) (add1 (var x)))) (-> num num) ()) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (λ (var x) (seq (app (var x) 7) (app (var x) (λ (var y) (var y))))) (? t) ()) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () () (s! (ref 0) (add1 0)) num ()) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (s! (ref 0) (λ (var x) 0)) num ()) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () () (s! (ref 0) (λ (var x) 0)) (-> num num) ()) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () () (let ([(var x) 0]) (var x)) num ()) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (let ([(var x) (λ (var y) (var y))]) (var x)) (-> num num) ()) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (let ([(var x) (λ (var y) (var y))]) 
                             (app (var x) 0)) 
                     num ()) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (let ([(var x) (λ (var y) (var y))])
                             (seq (app (var x) 0) 
                                  (app (var x) 0)))
                     num ()) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (let ([(var x) (λ (var y) (var y))])
                             (seq (app (var x) (var x)) 
                                  (app (var x) (add1 0))))
                     num ()) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (λ (var x) (add1 (app (! (var x)) 0))) (-> (ref (-> num num)) num) ()) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (λ (var x)
                             (seq (s! (var x) (λ (var z) 0))
                                  (add1 (app (! (var x)) 0))))
                     (-> (ref (-> num num)) num) ()) +inf.0)
 '())

;; ok
(check-equal?
 (generate (typeof-e () () (let ([(var x) (ref (λ (var y) (var y)))])
                             (seq (s! (var x) (λ (var z) 0))
                                  (add1 (app (! (var x)) 0))))
                     num ()) +inf.0)
 '())

;; not ok
(check-equal?
 (generate (typeof-e () () (let ([(var x) (ref (λ (var y) (var y)))])
                             (seq (s! (var x) (λ (var z) (λ (var a) (var a))))
                                  (add1 (app (! (var x)) 0))))
                     num ()) +inf.0)
 '())

(check-equal?
 (generate (typeof-e () () (let ([(var x) (λ (var a) (var a))])
                             (let ([(var y) (λ (var b) (add1 (var b)))])
                               (app (var x) 0)))
                     num ()) +inf.0)
 '())

;; check for stale variables
(check-equal?
 (generate (typeof-e () () (λ (var x)
                             (let ([(var x) 0])
                               (var x)))
                     (? t) ()) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () () (λ (var x2)
                              (app (let ([(var x3)
                                          (let ([(var x2) 0]) (var x2))])
                                     (var x3))
                                   (λ (var x4)
                                     (let ([(var x5) (λ (var x6) 0)])
                                       (let ([(var x7) 0])
                                         0)))))
                     (? t) ()) +inf.0)
 #f)

(check-equal?
 (generate (typeof-e () () (let ([(var x) 0])
                              (λ (var x) 0))
                      (? t) ())
            +inf.0)
 #f)

(define (generates-well-typed? size tries)
  (for/and ([_ (in-range tries)])
    (match (generate (typeof-e () () (? e) (? t) ()) size)
      [`( (t ,t) (e ,e) )
       (unless (generate (typeof-e () () ,e ,t ()) +inf.0)
         (pretty-print e)
         (pretty-print t)
         false)]
      [`( (e ,e) (t ,t) )
       (unless (generate (typeof-e () () ,e ,t ()) +inf.0)
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
  (pretty-print (fixup-vars (generate (typeof-e () () (? e) (? t) ()) size))))

(bound-measure 'depth)

; name clashes still a problem:
;> (generates-well-typed? 6 100)
;'(app
;  (let (((var #s(lvar y172302)) (λ (var #s(lvar x172307)) 0)))
;    (!
;     (app
;      (!
;       (let (((var #s(lvar y172259))
;              (ref (λ (var #s(lvar y172302)) (ref (var #s(lvar y172302)))))))
;         (var #s(lvar y172259))))
;      (s!
;       (let (((var #s(lvar x171932)) (ref 0))) (var #s(lvar x171932)))
;       (app (var #s(lvar y172302)) 0)))))
;  0)
;'num
;#f
;> (fixup-vars ...
;'(app
;  (let (((var y_0) (λ (var x_1) 0)))
;    (!
;     (app
;      (! (let (((var y_2) (ref (λ (var y_0) (ref (var y_0)))))) (var y_2)))
;      (s! (let (((var x_3) (ref 0))) (var x_3)) (app (var y_0) 0)))))
;  0)
;> 