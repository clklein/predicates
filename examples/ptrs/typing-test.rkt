#lang racket

(require "typing.rkt"
         "../../main.rkt"
         rackunit)

(define-syntax-rule (test-judgment-holds j)
  (check-not-false (solve j)))
(define-syntax-rule (test-judgment-does-not-hold j)
  (check-false (solve j)))
(define-syntax-rule (solve j)
  (parameterize ([current-permutations (λ (xs) xs)])
    (generate j +inf.0)))

; programs
(test-judgment-holds (well-typed-prog • (stmt (expr lit-int))))
(test-judgment-holds 
 (well-typed-prog •
                  ((var lit-int : int)
                   (stmt (expr (var z))))))
(test-judgment-does-not-hold 
 (well-typed-prog •
                  ((var lit-int : int)
                   (stmt (expr (app (var z) lit-int))))))
(test-judgment-holds 
 (well-typed-prog ((var lit-int : int) •)
                  (stmt (expr lit-int))))
(test-judgment-does-not-hold 
 (well-typed-prog ((var lit-int : (* int)) •)
                  (stmt (expr lit-int))))
(test-judgment-holds 
 (well-typed-prog ((fun (stmt (return (var z))) : int -> int) •)
                  (stmt (expr (app (var z) lit-int)))))
(test-judgment-holds 
 (well-typed-prog ((fun (stmt (return (& (var (s (s z)))))) : int -> (* int)) 
                   ((var lit-int : int) •))
                  (stmt (expr (* (app (var z) lit-int))))))
(test-judgment-holds 
 (well-typed-prog ((var lit-int : int) 
                   ((fun (stmt (return (& (var (s z))))) : int -> (* int)) •))
                  (stmt (expr (* (app (var (s z)) lit-int))))))
(test-judgment-holds 
 (well-typed-prog ((fun (stmt (return (app (var (s z)) (var z)))) : int -> int) •)
                  (stmt (expr (app (var z) lit-int)))))
(test-judgment-holds 
 (well-typed-prog ((fun (stmt (return (app (var (s (s z))) (var z)))) : int -> int)
                   ((fun (stmt (return (app (var (s z)) (var z)))) : int -> int) •))
                  (stmt (expr (app (var z) lit-int)))))

; seq statements
(test-judgment-holds (typeof-stmt • (seq (expr lit-int) (return lit-int)) int))
(test-judgment-does-not-hold (typeof-stmt • (seq (return lit-int) (return lit-int)) int))

; block statements
(test-judgment-holds 
 (typeof-stmt •
              (block ((var lit-int : int)
                      (stmt (return lit-int))))
              int))
(test-judgment-holds 
 (typeof-stmt •
              (block ((var lit-int : int)
                      (stmt (return (var z)))))
              int))
(test-judgment-holds 
 (typeof-stmt ((int -> (int -> int)) (int •))
              (block ((var (app (var z) (var (s z))) : (int -> int))
                      (stmt (return (app (var z) (var (s (s z))))))))
              int))
(test-judgment-does-not-hold 
 (typeof-stmt (int •)
              (block ((var (var z) : (int -> int))
                      (stmt (return lit-int))))
              int))
(test-judgment-does-not-hold 
 (typeof-stmt •
              (block ((var (var z) : int)
                      (stmt (return (app (var z) lit-int)))))
              int))

; if statements
(test-judgment-holds 
 (typeof-stmt (int •)
              (if (var z) 
                  (return (var z))
                  (return (var z)))
              int))
(test-judgment-does-not-hold 
 (typeof-stmt (int •)
              (if (var z) 
                  (return (var z))
                  (return))
              int))
(test-judgment-does-not-hold 
 (typeof-stmt (int •)
              (if (var z)
                  (return (& (var z)))
                  (return (var z)))
              int))

; return statement
(test-judgment-holds (typeof-stmt (int •) (return (var z)) int))
(test-judgment-does-not-hold (typeof-stmt (int •) (return (var z)) (* int)))
(test-judgment-holds (typeof-stmt • (return) void))
(test-judgment-does-not-hold (typeof-stmt • (return) int))

; expression statement
(test-judgment-holds (typeof-stmt (int •) (expr (var z)) void))
(test-judgment-does-not-hold 
 (typeof-stmt ((int -> int) •) (expr (app (var z) (var z))) void))

; literal ints
(test-judgment-holds (typeof-expr • lit-int int))
(test-judgment-does-not-hold (typeof-expr • lit-int (int -> int)))

; variables
(test-judgment-holds (typeof-expr (int •) (var z) int))
(test-judgment-holds
 (typeof-expr (int ((int -> int) •)) (var (s z)) (int -> int)))
(test-judgment-does-not-hold 
 (typeof-expr (int ((int -> int) •)) (var z) (int -> int)))

; address-of
(test-judgment-holds (typeof-expr (int •) (& (var z)) (* int)))
(test-judgment-does-not-hold (typeof-expr (int •) (& (var z)) (* (* int))))

; dereference
(test-judgment-holds (typeof-expr ((* int) •) (* (var z)) int))
(test-judgment-does-not-hold (typeof-expr ((* int) •) (* (var z)) (* int)))

; assignment
(test-judgment-holds (typeof-expr (int •) ((var z) := lit-int) int))
(test-judgment-does-not-hold (typeof-expr (int •) ((var z) := (& (var z))) int))
(test-judgment-holds (typeof-expr ((* int) •) ((* (var z)) := lit-int) int))
(test-judgment-holds
 (typeof-expr ((int -> (* int)) •)
              ((* (app (var z) lit-int)) := lit-int)
              int))
(test-judgment-does-not-hold
 (typeof-expr ((int -> (* int)) •)
              ((* (app (var z) lit-int)) := (var z))
              (* int)))

; application
(test-judgment-holds
 (typeof-expr ((int -> (* int)) •)
              (app (var z) lit-int)
              (* int)))
(test-judgment-does-not-hold
 (typeof-expr ((int -> (* int)) •)
              (app (var z) (var z))
              (* int)))

; int ops
(test-judgment-holds (typeof-expr • (lit-int + lit-int) int))
(test-judgment-does-not-hold (typeof-expr • (lit-int + lit-int) (* int)))
(test-judgment-holds 
 (typeof-expr •
              ((lit-int * lit-int) + (lit-int / lit-int))
              int))