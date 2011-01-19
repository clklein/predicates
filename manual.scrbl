#lang scribble/manual

@(require (for-label racket
                     "main.rkt")
          scribble/eval)

@(define example-evaluator (make-base-eval))
@(interaction-eval #:eval example-evaluator (require predicates rackunit))

@title{@racket[predicates] manual}

This collection provides a syntax for defining predicates inductively (e.g., typing rules) and
a tool for generating random objects that satisfy these predicates (e.g., typing derivations).

@defmodule[predicates]

@defform/subs[(define-predicate rule ...)
              ([rule [premise ...
                      conclusion
                      rule-name]]
               [premise (any-predicate term-template ...)]
               [conclusion (defined-predicate term-template ...)]
               [rule-name string]
               [term-template (code:line atomic-datum (code:comment "number, identifier, etc."))
                              (term-template ...)
                              (? identifier)
                              , term-expr])
              #:contracts ([bound-expr natural-number/c]
                           [term-expr term/c])]{
Defines @racket[defined-predicate] by induction. The definition consists of zero or more named rules,
each with a conclusion and zero or more premises. Each conclusion and premise consists of a predicate
name and zero or more @deftech{term-template}s. A @tech{term-template} of the form 
@racket[(? x)] matches any @tech{term}, instantiating @racket[x] to a fresh @racket[lvar]. 
A @tech{term-template} @racket[,e] is a Racket expression that evaluates to a @tech{term}.
  
For example, the following defines addition and multiplication on a unary encoding of natural numbers.
@examples[
#:eval example-evaluator
       (define-predicate
         [(sum z (? n) (? n))
          "sum-z"]
         [(sum (? m) (? n) (? o))
          (sum (s (? m)) (? n) (s (? o)))
          "sum-s"])
       (define-predicate
         [(prod z (? n) z)
          "prod-z"]
         [(prod (? m) (? n) (? o))
          (sum (? n) (? o) (? p))
          (prod (s (? m)) (? n) (? p))
          "prod-s"])]
}

@defthing[term/c contract/c]{
A @deftech{term} is either an atom, a list of @tech{terms}, or an @racket[lvar].
The @racket[generate] form matches @tech{terms} against the term templates in
predicate definitions and instantiates new terms from these templates.}

@defstruct[lvar ([id symbol?]) #:prefab]{
Holes in partially instantiated terms are represented by @racket[lvar]s.}
                                               
@defform[(generate (predicate term-template ...) bound-expr)
         #:contracts ([bound-expr positive?])]{
Randomly instantiates the @tech{term-templates} in a way that satisfies @racket[predicate],
returning an association list that maps the @tech{term-template}'s variables to @tech{terms}.

When @racket[bound-expr] does not evaluate to @racket[+inf.0], its value imposes a bound
space of instantiation considered. The @racket[bound-measure] parameter determines the 
interpretation of the bound.
  
For example, given the @racket[sum] and @racket[prod] definitions above, @racket[generate]
can find values for @racket[m] and @racket[n] that satisfy the equation @math{2 + m = 4 + n}.
@examples[
#:eval example-evaluator
       (generate (sum (s (s z)) (? n) (s (s (s (s (? m)))))) +inf.0)]
The result indicates that @math{n = 2 + m} is a solution for any @racket[m].

With a sufficiently restrictive search bound, @racket[generate] fails to find a solution
to the same equation.
@examples[
#:eval example-evaluator
       (generate (sum (s (s z)) (? n) (s (s (s (s (? m)))))) 2)]
  
The @tech{term-templates} supplied to @racket[generate] need not contain any variables.
This usage pattern is helpful when writing test cases for a predicate. For example,
the following test checks that @math{2 × 3 = 6}.

@examples[
#:eval example-evaluator
       (check-not-false
        (generate (prod (s (s z)) 
                        (s (s (s z)))
                        (s (s (s (s (s (s z)))))))
                 +inf.0))]
}
                                              
@defparam[bound-measure measure (or/c 'depth 'size)]{
When @racket[measure] is @racket['depth], @racket[generate] only considers instantiations
whose corresponding derivation trees have depth less than the given value; when @racket[measure]
is @racket['size] (the default), the derivation trees must have total size less than the given value.}

@defparam[revisit-solved-goals? revisit? boolean?]{
When @racket[revisit?] is non-@racket[false] (the default), @racket[generate] backtracks on 
decisions that lead to solved goals if it later fails to solve subsequent goals.

This backtracking pattern can occur, for example, in the following situation. If @racket[bound-measure]
is @racket['size], and @racket[generate] attempts to employ a rule with two premises, the derivation
of the first premise can consume too much of the overall derivation size to allow a derivation of the second
premise.}