#lang racket

(require (for-syntax racket/match
                     syntax/id-table))

(provide define-predicate
         generate
         solve
         unify
         disunify
         (struct-out lvar)
         term/c
         current-permutations
         make-permutations
         bound-measure
         revisit-solved-goals?
         unbounded-predicates
         user-goal-solver
         make-term
         solution
         make-rule
         cstrs
         cstrs-eqs
         cstrs-dqs
         check-and-resimplify
         neq)

(define-syntax-rule (generate (form-name . body) bound)
  (let ([visible (make-hash)])
    (form-name (make-term `body visible) (cstrs (hash) '()) bound
               (λ (env _1 _2) (solution visible env)) ;; dqs out?
               (λ () #f))))

(define (solution vars env)
  (hash-map vars (λ (x y) (list x (valuation (lvar y) env)))))

(define (valuation term env)
  (match term
    [(lvar x)
     (match (hash-ref (cstrs-eqs env) x (uninstantiated))
       [(uninstantiated) (lvar x)]
       [t (valuation t env)])]
    [(cons t u)
     (cons (valuation t env) (valuation u env))]
    [t t]))

(struct uninstantiated ())

(define-for-syntax (predicate-name conclusions def-form)
  (match (free-id-table-map 
          (for/fold ([m (make-immutable-free-id-table)])
                    ([c conclusions])
                    (syntax-case c ()
                      [(x . _) (free-id-table-set m #'x #t)]))
          (λ (k v) k))
    [(list name) name]
    [names (raise-syntax-error (syntax-e def-form) "inconsistent form name" #f #f names)]))

(define (make-term pre-term instantiations)
  (match pre-term
    [`(? ,x)
     (if (symbol? x)
         (lvar (hash-ref instantiations x
                         (λ () 
                           (define y (gensym x))
                           (hash-set! instantiations x y)
                           y)))
         (raise-type-error 'make-term "symbol" 0 x))]
    [(? list?)
     (for/list ([t pre-term]) (make-term t instantiations))]
    [_ pre-term]))

(define term/c
  (letrec ([term? (match-lambda
                    [`(? ,x) (symbol? x)]
                    [(? list? xs) (andmap term? xs)]
                    [_ #t])])
    (flat-contract term?)))

(define bound-measure (make-parameter 'size))
(define revisit-solved-goals? (make-parameter #t))

(define unbounded-predicates (make-parameter '()))
(define (unbounded-predicate? pred)
  (member pred (unbounded-predicates)))

(define-syntax (make-rule stx)
  (syntax-case stx ()
    [(_ ((prem-name . prem-body) ...) (conc-name . conc-body) rule-name instantiations def-form)
     #`(λ (term env bound succ fail)
         (match (unify term (make-term `conc-body instantiations) env)
           [#f (fail)]
           [env (let loop ([ps ((current-permutations)
                                (list (list prem-name (make-term `prem-body instantiations))
                                      ...))]
                           [env env]
                           [bound bound]
                           [fail fail])
                  (match ps
                    ['() (succ env bound fail)]
                    [(cons (list p b) ps’)
                     (p b env 
                        (if (unbounded-predicate? conc-name) bound (sub1 bound)) 
                        (λ (env bound’ fail’) 
                          (loop ps’ env 
                                (match (bound-measure)
                                  ['depth bound]
                                  ['size bound’])
                                (if (revisit-solved-goals?)
                                    fail’
                                    fail)))
                        fail)]))]))]))
  

(define-syntax (define-predicate stx)
  (syntax-case stx ()
    [(def-form (premises ... conclusion rule-name) ...)
     (with-syntax ([name (predicate-name (syntax->list #'(conclusion ...)) #'def-form)])
       #`(define (name term env bound succ fail)
           (define instantiations (make-hash))
           (if (or (positive? bound) (unbounded-predicate? name))
               (let loop ([rules ((current-permutations)
                                  (list (make-rule (premises ...) conclusion rule-name instantiations def-form) 
                                        ...))])
                 (match rules
                   ['() (fail)]
                   [(cons r rs)
                    (r term env bound succ (λ () (loop rs)))]))
               (match ((user-goal-solver) name (make-user-goal term env) env)
                 [#f (fail)]
                 [env (succ env bound fail)]))))]))

(define (neq term env bound succ fail)
  ;(display (format "neq: ~s\n" term))
  (match (disunify (first term) (second term) env)
           [#f (fail)]
           [env (succ env bound fail)]))

(define (make-user-goal term env)
  (let substitute ([t term])
    (cond [(lvar? t) (valuation t env)]
          [(cons? t) (map substitute t)]
          [else t])))

(define user-goal-solver (make-parameter (λ (pred term env) #f)))

;; term ::= atom | (lvar symbol) | (listof term)
;; env ::= (dict/c symbol term)
(struct lvar (id) #:prefab)

;; eqs : hash of lvar -> term
;; dqs : ( ((v1...vn)(t1...tn)) ... )
(struct cstrs (eqs dqs))

;; term term cstrs -> (or/c cstrs #f)
(define (unify t u cs)
  (let ([res (solve t u (cstrs-eqs cs))])
    (and res
         (check-and-resimplify (cstrs (car res) (cstrs-dqs cs))))))

;; cstrs -> cstrs
;; simplified - first element in lhs of all inequations is a var not occuring in lhs of eqns
(define (check-and-resimplify cs)
  (let loop ([dqs-notok (cstrs-dqs cs)]
             [dqs-ok '()])
    (cond
      [(or (empty? dqs-notok) (empty? (car dqs-notok)))
       cs]
      [(hash-has-key? (cstrs-eqs cs) (lvar-id (caaar dqs-notok)))
       ;; resimplifying currently causes infinite looping
       (disunify (caar dqs-notok) (cadar dqs-notok) (struct-copy cstrs cs
                                                                 [dqs (append (cdr dqs-notok) dqs-ok)]))]
      [else
       (loop (cdr dqs-notok) (cons (first dqs-notok) dqs-ok))])))


;; term term cstrs -> (or/c cstrs #f)
(define (disunify t u cs-in)
  (let* ([cs cs-in #|(check-and-resimplify cs-in)|#] ;; what if we end up here during a resimplification?
         [res (solve t u (cstrs-eqs cs))])
    (cond
      [(not res) cs]
      [(empty? (hash-keys (cdr res))) #f]
      [else (struct-copy cstrs cs
                         [dqs (cons (for/fold ([dq '(()())])
                                      ([(l r) (in-hash (cdr res))])
                                      `(,(cons (lvar l) (first dq)) ,(cons r (second dq))))
                                    (cstrs-dqs cs))])])))

;; solve : term term env -> (or/c (eqs-hash . new-eqs-hash) #f)
(define (solve t u e)
  (define new-e (hash)) ; new constraint eqns - for disunify
  (define (resolve t)
    (match t
      [(lvar x)
       (match (hash-ref e x (uninstantiated))
         [(uninstantiated) (lvar x)]
         [(lvar y) 
          (let ([t (resolve (lvar y))])
            (set! e (hash-set e x t)) ; these don't go in new-e because they aren't generated by the new unification
            t)]
         [u u])]
      [_ t]))
  (define (occurs? x t)
    (match t
      [(lvar y) (equal? x y)]
      [(cons t1 t2)
       (or (occurs? x (resolve t1))
           (occurs? x (resolve t2)))]
      [_ #f]))
  (and (let recur ([t’ (resolve t)] [u’ (resolve u)])
         (define (instantiate x t)
           (unless (and (lvar? t) (equal? x (lvar-id t)))
             (and (not (occurs? x t))
                  (set! new-e (hash-set new-e x t))
                  (set! e (hash-set e x t)))))
         (match* (t’ u’)
                 [((lvar x) _)
                  (instantiate x u’)]
                 [(_ (lvar x))
                  (instantiate x t’)]
                 [((cons t1 t2) (cons u1 u2))
                  (and (recur (resolve t1) (resolve u1))
                       (recur (resolve t2) (resolve u2)))]
                 [(_ _) (equal? t’ u’)]))
       (cons e new-e)))

(define (random-permutation lst)
  (let ([vec (list->vector lst)])
    (for ([i (in-range 0 (- (vector-length vec) 1))])
         (let* ([top-pos (- (vector-length vec) i 1)]
                [j (random (+ top-pos 1))]
                [tmp (vector-ref vec j)])
           (vector-set! vec j (vector-ref vec top-pos))
           (vector-set! vec top-pos tmp)))
    (vector->list vec)))

(define current-permutations
  (make-parameter random-permutation))

(define (make-permutations specs)
  (λ (list)
    (match specs
      ['() (error 'make-permutations "out of permutations")]
      [(cons s ss)
       (unless (equal? (length s) (length list))
         (error 'make-permutations
                "wrong size permutation: got ~s but expected ~s"
                (length s) (length list)))
       (unless (equal? (sort s <) (build-list (length s) values))
         (error 'make-permtuations "not a permutation: ~s" s))
       (set! specs ss)
       (map (curry list-ref list) s)])))