#lang racket

(require "lp3.rkt"
         "imp-poly/reduction.rkt"
         "imp-poly/typing.rkt"
         rackunit
         redex/reduction-semantics)

(provide (all-defined-out))

(define (to-redex exp)
  (match exp
    [`(app ,e1 ,e2)
     `(,(to-redex e1) ,(to-redex e2))]
    [`(λ (var ,x) ,e)
     `(λ ,x ,(to-redex e))]
    [`(let ([(var ,x) ,ex]) ,e)
     `(let (,x ,(to-redex ex)) ,(to-redex e))]
    [`(s! ,e1 ,e2)
     `(,(to-redex e1) := ,(to-redex e2))]
    [`(var ,x)
     x]
    [`(,es ...)
     (map to-redex es)]
    [else
     exp]))

(define (gen-e size)
  (match (fixup-vars (generate (typeof-e () () (? e) (? t)) size))
    [`((e ,e) (t ,t))
     (to-redex e)]
    [`((t ,t) (e ,e))
     (to-redex e)]))

(define (show-tc-eval size)
  (define e (gen-e size))
  (pretty-print e)
  (pretty-print (term (typeof () ,e)))
  (evaluate (term ,e)))

(define (gen-tc-eval size tries)
  (let loop ([stuck-count 0]
             [succs 0])
    (if (succs . < . tries)
        (let ()
          (define e (with-handlers ([string? (lambda (v) 'fail)])
                      (gen-e size)))
          (cond 
            [(equal? e 'fail) 
             (loop (add1 stuck-count) succs)]
            [else 
             (when (or (equal? (term (typeof () ,e)) #f)
                       (equal? (evaluate (term ,e)) 'stuck))
               (pretty-print e)
               (pretty-print (term (typeof () ,e)))
               (pretty-print (evaluate (term ,e))))
             (loop stuck-count (add1 succs))]))
        (printf "successes: ~s stuck generations: ~s\n" succs stuck-count))))

(define (gen-indef size)
  (define stuck-count 0)
  (define succs 0)
  (with-handlers ([(λ (_) #t)
                   (λ (e) (let () (printf "successes: ~s stuck generations: ~s\n" succs stuck-count) (raise e)))])
    (let loop ()
      (define e (with-handlers ([string? (lambda (v) 'fail)])
                  (gen-e size)))
      (cond 
        [(equal? e 'fail)
         (set! stuck-count (add1 stuck-count))
         (loop)]
        [else 
         (when (or (equal? (term (typeof () ,e)) #f)
                   (equal? (evaluate (term ,e)) 'stuck))
           (pretty-print e)
           (pretty-print (term (typeof () ,e)))
           (pretty-print (evaluate (term ,e))))
         (set! succs (add1 succs))
         (loop)]))))
    
;; bug found ~1 hour :
;;;'(λ x_1 ((! (! (ref x_1))) := (let (x_1 (! x_1)) x_1)))
;;;#f
;;;'(λ x_1 ((! (! (ref x_1))) := (let (x_1 (! x_1)) x_1)))

;; evals, doesn't check
(check-equal?
 (evaluate (term ((λ x_1 ((! (! (ref x_1))) := (let (x_1 (! x_1)) x_1))) (ref (ref 0)))))
 0)

(check-equal?
 (term (typeof () ((λ x_1 ((! (! (ref x_1))) := (let (x_1 (! x_1)) x_1))) (ref (ref 0)))))
 #f)
