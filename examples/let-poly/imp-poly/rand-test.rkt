#lang racket

(require (only-in "lang.rkt" Λs)
         (only-in "typing.rkt" typeof)
         (only-in "reduction.rkt" evaluate)
         redex/reduction-semantics)
(provide main)

(define (main . args)
  (define-values (max-depth hint tests-per-round)
    (parse-args args))
  (let loop ([total-tests 0])
    (displayln total-tests)
    (define-syntax-rule (do-tests template)
      (test-soundness template
                      tests-per-round
                      (λ (round-so-far)
                        (inexact->exact
                         (min max-depth
                              (default-attempt-size 
                                (+ total-tests round-so-far)))))))
    (define result 
      (match hint
        ['none (do-tests e_1)]
        ['weak (do-tests (let (a (ref e_2)) e_1))]
        ['strong (do-tests (let (a (ref (λ a a))) e_1))]))
    (if (counterexample? result)
        result
        (loop (+ total-tests tests-per-round)))))

(define (parse-args args)
  (define max-depth +inf.0)
  (define hint 'none)
  (define log-freq 50000)
  (command-line #:once-each
                [("--max-depth") d
                                 "Limit parse tree depth to d"
                                 (set! max-depth (string->number d))]
                [("--log-freq") n
                                "Print completed count every n tests"
                                (set! log-freq (string->number n))]
                #:once-any
                [("--strong-hint") "Start tests with let r = ref(λx.x) in ..."
                                   (set! hint 'strong)]
                [("--weak-hint") "Start tests with let r = ref(e) in ..."
                                 (set! hint 'weak)])
  (values max-depth hint log-freq))

(define-syntax-rule (test-soundness template attempts attempt-size)
  (let ()
    (define-extended-language gen-lang Λs
      (x a b c d w y z))
    (redex-check gen-lang (name e template)
                 (or (not (term (typeof () e)))
                     (not (equal? 'stuck (evaluate (term e)))))
                 #:attempts attempts
                 #:attempt-size attempt-size
                 #:prepare close
                 #:print? false)))

(define (close e)
  (let C ([expr e] [bound '()])
    (match expr
      [(? variable?)
       (cond [(member expr bound) expr]
             [(empty? bound) (random-constant)]
             [else (random-member bound)])]
      [`(λ ,x ,e)
       `(λ ,x ,(C e (cons x bound)))]
      [`(let (,x ,r) ,b)
       `(let (,x ,(C r bound)) ,(C b (cons x bound)))]
      [(? list?)
       (for/list ([t expr]) (C t bound))]
      [_ expr])))

(define variable? (redex-match Λs x))

(define (random-member xs)
  (list-ref xs (random (length xs))))

(define random-constant
  (let ()
    (define-language constants
      (k number (λ a a) (λ a k) (ref k)))
    (define generator (generate-term constants k))
    (λ () (generator 3))))