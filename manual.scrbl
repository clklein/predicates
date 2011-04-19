#lang scribble/manual

@(require (for-label racket
                     "main.rkt")
          planet/scribble
          scribble/eval)

@(define example-evaluator (make-base-eval))
@(interaction-eval 
  #:eval example-evaluator 
  (require "main.rkt" rackunit racket/match))

@title{@racket[predicates] manual}

This collection provides a syntax for defining predicates inductively (e.g., typing rules) and
a tool for generating random objects that satisfy these predicates (e.g., typing derivations).

@defmodule/this-package[main]

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

@defparam[unbounded-predicates predicates (listof procedure?)]{
Configures @racket[bound-measure] to ignore the depth/size of derivations of the
forms in @racket[predicates] (default @racket[empty]).

@examples[
#:eval example-evaluator
       (define-predicate
         [(p)
          (q)
          "q"])
       (define-predicate
         [(p)
          "p"])
       (generate (q) 1)
       (parameterize ([unbounded-predicates (list p)])
         (generate (q) 1))]
}

@defparam[user-goal-solver solver (-> procedure? term/c (hash/c symbol? term/c)
                                      (or/c #f (hash/c symbol? term/c)))]{
Specifies a procedure @racket[solver] to be tried before backtracking when the
depth/size bound is zero. 

The procedure receives a predicate (to identify the goal's form), a single 
@tech{term} representing the predicate's arguments, and a hash mapping the 
names of (instantiated) @racket[lvar]s to @tech{terms}. When the @tech{term}
supplied as the second argument contains @racket[lvar]s, those variables
are totally uninstantiated, but when an @racket[lvar] appears in the range
of the third argument, that variable may already be instantiated (i.e., it
may be in the domain of the third argument).

To indicate that it has solved the goal, the procedure returns an extension
of the third argument (instantiating any variables necessary). The procedure
may return @racket[#f] to indicate that it could not solve the goal.

The default value for @racket[solver] solves no goals.

@examples[
#:eval example-evaluator
       (define-predicate
         [(q a (? x))
          (p (? x))
          "p"])
       (define-predicate
         [(q (? x) (? y))
          "q"])
       (generate (p (? x)) 1)
       (parameterize ([user-goal-solver 
                       (λ (pred term map)
                         (and (equal? pred q)
                              (match term
                                [(list 'a (lvar y))
                                 (hash-set map y 'b)])))])
         (generate (p (? x)) 1))]
}

@defparam[current-permutations permuter (-> list? list?)]{
The @racket[permuter] procedure determines the order in which @racket[generate]
considers rules and attempts to establish premises. The procedure receives
lists of (opaque) rules/premises and returns them in the order in which they
should be used. The procedure's default value returns a random permutation. 
Supplying the identity function makes @racket[generate] behave like Prolog.
}                                                                         
                                                                         
@defparam[revisit-solved-goals? revisit? boolean?]{
When @racket[revisit?] is non-@racket[false] (the default), @racket[generate] backtracks on 
decisions that lead to solved goals if it later fails to solve subsequent goals.

This backtracking pattern can occur, for example, in the following situation. If @racket[bound-measure]
is @racket['size], and @racket[generate] attempts to employ a rule with two premises, the derivation
of the first premise can consume too much of the overall derivation size to allow a derivation of the second
premise.}