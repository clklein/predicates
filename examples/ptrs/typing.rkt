#lang racket

(require "../../main.rkt")
(provide (all-defined-out))

;; p ::= (ds b)
;; ds ::= • | (d ds)
;; d ::= (fun b : t -> t) | (var e : t)
;; b ::= (stmt s) | ((var e : t) b)
;; s ::= (block b) | (seq s s) | (if e s s) | (return) | (return e) | (expr e)
;; e ::= (e bop e) | (app e e) | (lv := e) | (* e) | (& x) | x | lit-int
;; lv ::= x | (* e)
;; x ::= (var n)
;; n :: = z | (s n)
;; bop ::= + | - | * | / | > | < | == | !=
;; t ::= int | void | (t -> t) | (* t)
;; Γ ::= • | (t Γ)

; (well-typed-prog ds b)
(define-predicate
  [(types-of-defs (? ds) (? Γ))   ; would like to solve this goal
   (defs-have-types (? Γ) (? ds)) ; before this goal
   (typeof-block (? Γ) (? b) (? t))
   (well-typed-prog (? ds) (? b))
   "prog"])

; (types-of-defs ds Γ)
(define-predicate
  [(types-of-defs • •)
   "type-of-no-def"]
  [(types-of-defs (? ds) (? ts))
   (types-of-defs 
     ((fun (? b) : (? t1) -> (? t2)) (? ds))
     (((? t1) -> (? t2)) (? ts)))
   "type-of-fun-def"]
  [(types-of-defs (? ds) (? ts))
   (types-of-defs 
     ((var (? e) : (? t)) (? ds))
     ((? t) (? ts)))
   "type-of-var-def"])

; (defs-have-types Γ ds)
(define-predicate
  [(defs-have-types (? Γ) •)
   "no-def-has-type"]
  [(typeof-block ((? t1) (? Γ)) (? b) (? t2))
   (defs-have-types (? Γ) (? ds))
   (defs-have-types
    (? Γ)
    ((fun (? b) : (? t1) -> (? t2)) (? ds)))
   "fun-def-has-type"]
  [(typeof-expr (? Γ) (? e) (? t))
   (defs-have-types (? Γ) (? ds))
   (defs-have-types
    (? Γ)
    ((var (? e) : (? t)) (? ds)))
   "var-def-has-type"])

; (typeof-block Γ b t)
(define-predicate
  [(typeof-stmt (? Γ) (? s) (? t))
   (typeof-block (? Γ) (stmt (? s)) (? t))
   "typeof-stmt-block"]
  [(typeof-expr (? Γ) (? e) (? u))
   (typeof-block ((? u) (? Γ)) (? b) (? t))
   (typeof-block (? Γ) ((var (? e) : (? u)) (? b)) (? t))
   "typeof-def-block"])

; (typeof-stmt Γ s t)
(define-predicate
  [(typeof-block (? Γ) (? b) (? t))
   (typeof-stmt (? Γ) (block (? b)) (? t))
   "typeof-block-stmt"]
  [(typeof-stmt (? Γ) (? s1) void)
   (typeof-stmt (? Γ) (? s2) (? t))
   (typeof-stmt (? Γ) (seq (? s1) (? s2)) (? t))
   "typeof-seq-stmt"]
  [(typeof-expr (? Γ) (? e) int)
   (typeof-stmt (? Γ) (? s1) (? t))
   (typeof-stmt (? Γ) (? s2) (? t))
   (typeof-stmt (? Γ) (if (? e) (? s1) (? s2)) (? t))
   "typeof-if-stmt"]
  [(typeof-stmt (? Γ) (return) void)
   "typeof-void-return-stmt"]
  [(typeof-expr (? Γ) (? e) (? t))
   (typeof-stmt (? Γ) (return (? e)) (? t))
   "typeof-return-stmt"]
  [(typeof-expr (? Γ) (? e) (? t))
   (typeof-stmt (? Γ) (expr (? e)) void)
   "typeof-expr-stmt"])

; (typeof-expr Γ e)
(define-predicate
  [(bop (? s))
   (typeof-expr (? Γ) (? e1) int)
   (typeof-expr (? Γ) (? e2) int)
   (typeof-expr (? Γ) ((? e1) (? s) (? e2)) int)
   "typeof-bop"]
  [(typeof-expr (? Γ) (? e1) ((? t2) -> (? t)))
   (typeof-expr (? Γ) (? e2) (? t2))
   (typeof-expr (? Γ) (app (? e1) (? e2)) (? t))
   "typeof-app"]
  [(lv (? e1))
   (typeof-expr (? Γ) (? e1) (? t))
   (typeof-expr (? Γ) (? e2) (? t))
   (typeof-expr (? Γ) ((? e1) := (? e2)) (? t))
   "typeof-asgn"]
  [(typeof-expr (? Γ) (? e1) (* (? t)))
   (typeof-expr (? Γ) (* (? e1)) (? t))
   "typeof-deref"]
  [(var-has-type (? Γ) (? x) (? t))
   (typeof-expr (? Γ) (& (var (? x))) (* (? t)))
   "typeof-addr"]
  [(var-has-type (? Γ) (? x) (? t))
   (typeof-expr (? Γ) (var (? x)) (? t))
   "typeof-var"]
  [(typeof-expr (? Γ) lit-int int)
   "typeof-lit-int"])

; (var-has-type Γ n)
(define-predicate
  [(var-has-type ((? t) (? Γ)) z (? t))
   "this-var"]
  [(var-has-type (? Γ) (? n) (? t))
   (var-has-type ((? u) (? Γ)) (s (? n)) (? t))
   "another-var"])

; (bop symbol)
(define-predicate
  [(bop +)
   "int+"]
  [(bop -)
   "int-"]
  [(bop *)
   "int*"]
  [(bop /)
   "int/"]
  [(bop >)
   "int>"]
  [(bop <)
   "int<"]
  [(bop ==)
   "int=="]
  [(bop !=)
   "int!="])

;; (lv e)
(define-predicate
  [(lv (var (? x)))
   "lv-var"]
  [(lv (* (? e)))
   "lv-ptr"])