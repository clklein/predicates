#lang racket

(require "predicates.rkt"
         rackunit)

(define (table env)
  (sort (dict-map env cons)
        string<=?
        #:key (curry format "~s")))

(let ()
  (define-predicate
    [(plus z (? y) (? y))
     "plus-z"]
    [(plus (? x) (? y) (? z))
     (plus (s (? x)) (? y) (s (? z)))
     "plus-s"])
  
  (check-equal? (generate (plus z (s z) (? q)) 1)
                '((q (s z))))
  
  (check-equal? (generate (plus (s (s z)) z (? q)) 3)
                '((q (s (s z)))))
  (check-equal? (generate (plus (s z) z (? q)) 1) #f)
  
  (parameterize ([current-permutations
                  ; plus-z
                  (make-permutations '((0 1) ()))])
    (check-equal? (table (generate (plus (? x) (? y) (s (s z))) 3))
                  '((x z) (y (s (s z))))))
  (parameterize ([current-permutations
                  ; plus-s (plus-s plus-z)
                  (make-permutations '((1 0) (0) (1 0) (0) (0 1) ()))])
    (check-equal? (table (generate (plus (? x) (? y) (s (s z))) 3))
                  '((x (s (s z))) (y z))))
  (parameterize ([current-permutations
                  ; plus-s plus-z
                  (make-permutations '((1 0) (0) (0 1) ()))])
    (check-equal? (table (generate (plus (? x) (? y) (s (s z))) 3))
                  '((x (s z)) (y (s z)))))
  
  (parameterize ([current-permutations
                  ; plus-s (plus-s plus-z)
                  ; but not before trying
                  ; plus-z, 
                  ; plus-s plus-z, and 
                  ; plus-s (plus-s (plus-s plus-z))
                  (make-permutations '((0 1) (0) (0 1) (0) (1 0) ()))])
    (check-equal? (table (generate (plus (? x) z (s (s z))) 3))
                  '((x (s (s z)))))))

(let ()
  (define-predicate
    [(eq (? x) (? x))
     "eq"])
  (check-equal? (generate (eq (? x) (cons 1 (? x))) +inf.0) #f)
  (check-not-false (generate (eq (? x) (? x)) +inf.0)))

(let ()
  (define-predicate
    [(r2 (? x))
     (r3 (? x))
     (r1 (? x))
     "r1"])
  (define-predicate
    [(r2 (? x))
     "r2"])
  (define-predicate
    [(r3 (? x))
     "r3a"]
    [(r3 (? x))
     (r3 (? x))
     "r3b"])
  
  ; revists a choice that consumes too much of the size bound
  (parameterize ([current-permutations
                  (make-permutations
                   '(; only r1 rule
                     (0)
                     ; premises right to left
                     (1 0)
                     
                     ; r3b first
                     (1 0)
                     ; only premise
                     (0)
                     ; r3a first this time
                     (0 1)
                     ; no premises
                     ()
                     
                     ; no size remains for r1's other premise
                     ; backtrack to r3b for r3b's premise
                     ; only r3b premise
                     (0)
                     ; size exhausted again
                     
                     ; now try r3a
                     ; no premises
                     ()
                     
                     ; only r2 rule
                     (0)
                     ; no premises
                     ()))])
    (check-not-false (generate (r1 (? x)) 3)))
  
  ; same choice may succeed with bound interpreted as depth
  (parameterize ([current-permutations
                  (make-permutations
                   '(; only r1 rule
                     (0)
                     ; premises right to left
                     (1 0)
                     
                     ; r3b first
                     (1 0)
                     ; only premise
                     (0)
                     ; r3a first this time
                     (0 1)
                     ; no premises
                     ()
                     
                     ; only r2 rule
                     (0)
                     ; no premises
                     ()))]
                 [bound-measure 'depth])
    (check-not-false (generate (r1 (? x)) 3)))
  
  (parameterize ([current-permutations
                  (make-permutations
                   '(; only r1 rule
                     (0)
                     ; premises right to left
                     (1 0)
                     
                     ; r3b first
                     (1 0)
                     ; only premise
                     (0)
                     
                     ; depth exhausted
                     ; try r3a instead
                     
                     ; no premises
                     ()
                     
                     ; now return to r1's other premise
                     ; only r2 rule
                     (0)
                     
                     ; no premises
                     ()))]
                 [bound-measure 'depth])
    (check-not-false (generate (r1 (? x)) 2))))

(let ()
  (define-predicate
    [(r2 (? x))
     (r3 (? x))
     (r1 (? x))
     "r1"])
  (define-predicate
    [(eq (? x) a)
     (r2 (? x))
     "r2a"]
    [(eq (? x) b)
     (r2 (? x))
     "r2b"])
  (define-predicate
    [(r3 b)
     "r3"])
  (define-predicate
    [(eq (? x) (? x))
     "eq"])
  
  ; revists a choice that instantiates a variable in an dead-end way
  (parameterize ([current-permutations
                  (make-permutations
                 '(; only r1 rule
                   (0)
                   ; premises left to right
                   (0 1)
                   
                   ; r2a first
                   (0 1)
                   ; only premise
                   (0)
                   ; only eq rule
                   (0)
                   ; no premises
                   ()
                   
                   ; only r3 rule
                   (0)
                   ; fail
                   
                   ; only r2b premise
                   (0)
                   ; only eq rule
                   (0)
                   ; no premises
                   ()
                   
                   ; only r3 rule
                   (0)
                   ; no premises
                   ()))])
    (check-not-false (generate (r1 (? x)) +inf.0)))
  
  ; same example without reconsidering the r2 derivation
  (parameterize ([current-permutations
                  (make-permutations
                   '(; only r1 rule
                     (0)
                     ; premises left to right
                     (0 1)
                     
                     ; r2a first
                     (0 1)
                     ; only premise
                     (0)
                     ; only eq rule
                     (0)
                     ; no premises
                     ()
                     
                     ; only r3 rule
                     (0)))]
                 [revisit-solved-goals? #f])
    (check-false (generate (r1 (? x)) +inf.0)))
  
  ; but other rules are still tried when one fails
  (parameterize ([current-permutations
                  (make-permutations
                   '(; only r1 rule
                     (0)
                     ; premises left to right
                     (0 1)
                     
                     ; r2a first
                     (0 1)
                     ; only premise
                     (0)
                     ; only eq rule
                     (0)
                     
                     ; does not unify
                     ; now try r2b
                     
                     ; only premise
                     (0)
                     ; only eq rule
                     (0)
                     ; no premises
                     ()
                     
                     ; now turn to r1's other premise
                     
                     ; only r3 rule
                     (0)
                     ; no premises
                     ()))]
                 [revisit-solved-goals? #f])
    (check-not-false (generate (r1 b) +inf.0))))

; unbounded-predicates
(let ()
  (define-predicate
    [(q (? x))
     (p (? x))
     "p"])
  (define-predicate
    [(q a)
     "qa"]
    [(r)
     (q b)
     "qb"])
  (define-predicate
    [(r)
     "r"])
  (check-false (generate (p a) 1))
  (parameterize ([unbounded-predicates (list q)])
    (check-not-false (generate (p a) 1)))
  (parameterize ([unbounded-predicates (list q)])
    (check-false (generate (p b) 1)))
  (parameterize ([unbounded-predicates (list q r)])
    (check-not-false (generate (p b) 1))))

; user-goal-solver
(let ()
  (define-predicate
    [(q a (? x))
     (p (? x))
     "p"])
  (define-predicate
    [(q (? x) (? y))
     "q"])
  (check-false (generate (p (? x)) 1))
  (parameterize ([user-goal-solver (λ (p t e) #f)])
    (check-false (generate (p (? x)) 1)))
  (parameterize ([user-goal-solver 
                  (λ (p t e)
                    (and (equal? p q)
                         (match t
                           [(list 'a (lvar y))
                            (hash-set e y 'b)])))])
    (check-equal? (generate (p (? x)) 1) '((x b)))))

(let ()
  (define-predicate
    [(eq (? x) ,'a)
     (r ,'(? x))
     "r"])
  (define-predicate
    [(eq (? x) (? x))
     "eq"])
  (check-equal? (generate (r (? ,'y)) +inf.0)
                '((y a))))

(define-syntax (test-solve stx)
  (syntax-case stx ()
    [(_ t u e e’)
     (quasisyntax/loc stx
       (check-equal? 
        (cond [(solve `t `u (make-immutable-hash `e)) => table]
              [else #f])
        #,(syntax-case #'e’ ()
            [#f #'#f]
            [_ #`(table (make-immutable-hash `e’))])))]))

(test-solve 1 1 ((x . 3)) ((x . 3)))
(test-solve 1 2 () #f)
(test-solve (cons 1 2) (cons 1 2)
            ((x . 3))
            ((x . 3)))
(test-solve (cons 1 2) (cons 1 3) () #f)
(test-solve ,(lvar 'x) 3
            ((x . 3))
            ((x . 3)))
(test-solve ,(lvar 'x) 3
            ((x . ,(lvar 'y)) (y . 3))
            ((x . 3) (y . 3)))
(test-solve ,(lvar 'x) 4
            ((x . 3))
            #f)
(test-solve ,(lvar 'x) 3
            ((x . ,(lvar 'y)) (y . 4))
            #f)
(test-solve ,(lvar 'x)
            (cons 1 ,(lvar 'x))
            ()
            #f)
(test-solve ,(lvar 'y)
            (cons 1 ,(lvar 'x))
            ((x . ,(lvar 'y)) (y . ,(lvar 'z)))
            #f)
(test-solve (cons ,(lvar 'x) ,(lvar 'x))
            (cons (cons 1 ,(lvar 'y)) (cons ,(lvar 'y) 1))
            ()
            ((x . (cons 1 ,(lvar 'y))) (y . 1)))
(test-solve (cons ,(lvar 'x) ,(lvar 'x))
            (cons (cons 1 ,(lvar 'y)) (cons ,(lvar 'y) 2))
            ()
            #f)
(test-solve (cons ,(lvar 'x) (cons ,(lvar 'y) (cons ,(lvar 'z) (cons ,(lvar 'x) ,(lvar 'y)))))
            (cons ,(lvar 'y) (cons ,(lvar 'z) (cons 0 (cons 0 0))))
            ()
            ((x . 0) (y . 0) (z . 0)))
(test-solve (cons ,(lvar 'x) (cons ,(lvar 'y) (cons ,(lvar 'z) ,(lvar 'x))))
            (cons ,(lvar 'y) (cons ,(lvar 'z) (cons 0 1)))
            ()
            #f)
