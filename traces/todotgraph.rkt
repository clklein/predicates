#lang racket

(require "../predicates.rkt")

(provide write-trace-to-file)

(debug-out? #t)

(define (make-tree trace)
  (let loop ([tree (vector 0)]
             [t trace])
    (match t
      [`((,loc ,name ,state ,term ,body ,bound ,depth) ,remaining-traces ...)
       (loop (insert-node loc name (positive? bound) term tree) remaining-traces)]
      [else
       tree])))

(define (insert-node loc label in-bound term tree)
  (match loc
    [`(,i ,is ...)
     (if (< (vector-length tree) (+ i 2))
         (let ([new-node (make-vector (+ i 2))])
           (vector-copy! new-node 0 tree)
           (vector-set! new-node (+ i 1) (insert-node is label in-bound term (vector-ref new-node (+ i 1))))
           new-node)
         (let ()
           (vector-set! tree (+ i 1) (insert-node is label in-bound term (vector-ref tree (+ i 1))))
           tree))]
    ['()
     (vector (list label (gensym) in-bound term))]
    [else (error "insert-node fail")]))

(define (to-dot-format tree out)
  (define (write-edges name leaves)
    (for ([l leaves])
      (unless (equal? l 0)
        (let ([leaf (vector-ref l 0)])
          (display (format "~a [label=\"~a\"]\n" (second name) (first name)) out)
          (unless (third name) (display (format "~a [color=red]\n" (second name)) out))
          (display (format "~a [label=\"~a\"]\n" (second leaf) (first leaf)) out)
          (unless (third leaf) (display (format "~a [color=red]\n" (second leaf)) out))
          (display (format "~a -> ~a\n" (second name) (second leaf)) out)))))
  (match tree
    [`#(,name)
     (void)]
    [`#(,name ,leaves ...)
     (let () 
       (write-edges name leaves)
       (map (lambda (l) (to-dot-format l out)) leaves))]
    [0 
     (void)]))

(define (trace-to-dot trace out)
  (let ([steps (length trace)])
    (for ([i (in-range 1 (+ steps 1))])
      (let ()
        (display (format "\ndigraph trace~s {\nratio=compress;\nsize=\"8.5,11\";\n" i) out)
        (to-dot-format (make-tree (take trace i)) out)
        (display "}\n" out)))))

(define (write-trace-to-file filename)
  (call-with-output-file filename
    (lambda (out) (trace-to-dot (gen-trace) out))))

