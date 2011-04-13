#lang racket

(require (for-syntax racket/match
                     syntax/id-table))

(provide define-predicate
         generate
         solve
         (struct-out lvar)
         term/c
         current-permutations
         make-permutations
         bound-measure
         revisit-solved-goals?
         
         no-bound-rules
         user-goal-solver)

(define-syntax-rule (generate (form-name . body) bound)
  (let ([visible (make-hash)])
    (form-name (make-term `body visible) (hash) bound
               (λ (env _1 _2) (solution visible env))
               (λ () #f))))

(define (solution vars env)
  (define extract
    (match-lambda
      [(lvar x)
       (match (hash-ref env x (uninstantiated))
         [(uninstantiated) (lvar x)]
         [t (extract t)])]
      [(cons t u) (cons (extract t) (extract u))]
      [t t]))
  (hash-map vars (λ (x y) (list x (extract (lvar y))))))

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

(define no-bound-rules (make-parameter '()))
(define (no-bound? rule-name)
  (member rule-name (no-bound-rules)))

(define-syntax (make-rule stx)
  (syntax-case stx ()
    [(_ ((prem-name . prem-body) ...) (conc-name . conc-body) rule-name instantiations def-form)
     #`(λ (term env bound succ fail)
         (match (solve term (make-term `conc-body instantiations) env)
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
                        (if (no-bound? 'conc-name) bound (sub1 bound)) 
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
           (if (or (positive? bound) (no-bound? 'name))
               (let loop ([rules ((current-permutations)
                                  (list (make-rule (premises ...) conclusion rule-name instantiations def-form) 
                                        ...))])
                 (match rules
                   ['() (fail)]
                   [(cons r rs)
                    (r term env bound succ (λ () (loop rs)))]))
               (match ((user-goal-solver) (make-user-goal (cons 'name term) env) env)
                 [#f (fail)]
                 [env (succ env bound fail)]))))]))

(define (make-user-goal term env)
  (define substitution
    (solution
     (make-immutable-hash
      (let vars ([t term])
        (match t
          [(lvar x) (list (cons x x))]
          [(? list?) (append-map vars t)]
          [_ empty])))
     env))
  (let substitute ([t term])
    (match t
      [(lvar x)
       (second (assoc x substitution))]
      [(? list?)
       (map substitute t)]
      [_ t])))

(define user-goal-solver (make-parameter (λ (term env) #f)))

;; term ::= atom | (lvar symbol) | (listof term)
;; env ::= (dict/c symbol term)
(struct lvar (id) #:prefab)

;; solve : term term env -> (or/c env #f)
(define (solve t u e)
  (define (resolve t)
    (match t
      [(lvar x)
       (match (hash-ref e x (uninstantiated))
         [(uninstantiated) (lvar x)]
         [(lvar y) 
          (let ([t (resolve (lvar y))])
            (set! e (hash-set e x t))
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
       e))

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