#lang racket

(require "typing.rkt"
         "../../predicates.rkt"
         rackunit)

(define integral
  '(loop ((>>> (arr (λ (p) ((+ (snd p)) ((* (fst p)) .01)))))
          ((>>> (init 0)) (arr (λ (x) (pair x x)))))))

(define fixA
  `(λ (f)
     (loop ((>>> (second f))
            (arr (λ (p) (pair (snd p) (snd p))))))))

(define exp
  `(,fixA ((>>> ,integral) (arr (+ 1)))))

(define loopB
  `(λ (i)
     (λ (f)
       (loop ((>>> f)
              (second (second (init i))))))))

(define-syntax-rule (choose variable judgment)
  (let ([sol-map (generate judgment +inf.0)])
    (and sol-map
         (second (assoc 'variable sol-map)))))

(check-equal? (choose τ (typeof • (unit) (? τ)))
              'unit)
(check-equal? (choose τ (typeof ((-> unit unit) (unit •)) (var (s z)) (? τ)))
              'unit)
(check-not-false (generate (typeof • (λ (var z)) (-> unit unit)) +inf.0))
(check-equal? (choose x (typeof ((pair unit unit) (unit •)) (var (? x)) unit))
              '(s z))

(check-equal? (generate (typeof ((-> unit unit) (unit •))
                                (var z)
                                unit)
                        +inf.0)
              #f)
(check-equal? (generate (typeof ((-> unit unit) (unit •))
                                (var (? x))
                                (pair unit unit))
                        +inf.0)
              #f)

(check-equal?
 (choose τ (typeof • 
                   ,(to-type-form integral)
                   (? τ)))
 '(arr num num))
(check-not-false
 (generate (typeof • ,(to-type-form fixA) (-> (arr num num) (arr unit num))) +inf.0))
(check-not-false
 (generate (typeof • ,(to-type-form exp) (arr unit num)) +inf.0))
(check-not-false
 (generate
  (typeof •
          ,(to-type-form loopB)
          (-> num
              (-> (arr (pair unit (pair (pair num num) num))
                       (pair (pair unit unit) (pair (pair num num) num)))
                  (arr unit (pair unit unit)))))
  +inf.0))
