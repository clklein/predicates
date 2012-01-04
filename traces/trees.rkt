#lang racket

(require racket/math
         racket/draw
         racket/gui)

(provide (all-defined-out))

;; tree browser prototype
;;
;; to browse a random tree, just use (random-tree)
;; (building a tree is sometimes slow - the generation process is
;; unnecessarily complex to mimic the traces that come from the
;; program genreator)
;; 
;; uses a mapping to a geometric series to get an "axis at infinity" effect
;;
;; TODO:
;; * the layout algorithm is pretty dumb right now, could definitely be improved
;; * zooming/panning starts getting slow for trees with around 1,000 nodes

(struct gen-tree
  (attributes [children #:mutable])
  #:transparent)

(struct attributes
  (label id in-bound term coords)
  #:transparent)

(struct coords
  (x y)
  #:transparent
  #:mutable)

(struct trace-step (path b-factor attributes)
  #:transparent)

;; doesn't currently use all the information in the trace
(define (make-tree trace)
  (let loop ([tree (vector 0)]
             [t trace])
    (match t
      [`((,loc ,name ,state ,term ,body ,bound ,depth) ,remaining-traces ...)
       (define atts (attributes name (gensym) (positive? bound) term (coords #f #f)))
       (loop (insert-tree-node loc atts tree) remaining-traces)]
      [else
       tree])))

(define (insert-tree-node loc attributes tree-root)
  (define (insert-node loc attributes tree)
    (match loc
      [`(,i) ;; append or replace
       (cond [(= (vector-length (gen-tree-children tree)) i)
              (define new-children (vector-append (gen-tree-children tree)
                                                  (vector (gen-tree attributes (make-vector 0)))))
              (set-gen-tree-children! tree new-children)]
             [(< i (vector-length (gen-tree-children tree)))
              (vector-set! (gen-tree-children tree) i
                           (gen-tree attributes (make-vector 0)))]
             [else (error "tree update wasn't an append or replace")])]
      [`(,i ,is ...)
       (insert-node is attributes (vector-ref (gen-tree-children tree) i))]
      ['() ;; initial tree (or replacement)
       (set! tree-root (gen-tree attributes (make-vector 0)))]
      [else (error "tree didn't have expected generation pattern" loc tree)]))
  (insert-node loc attributes tree-root)
  tree-root)

(define (all-trees trace)
  (for/list ([i (length trace)]) (make-tree (take trace i))))
 
(define no-pen (new pen% [style 'transparent]))
(define no-brush (new brush% [style 'transparent]))
(define blue-brush (new brush% [color "Medium Sea Green"]))
(define red-pen (new pen% [color "Steel Blue"] [width 2]))

(define NODE-WIDTH 300)

(define (calculate-width-for-depth t this-depth max-depth)
  (match t
    [(gen-tree (attributes p b-f b l cs) '#())
     (* NODE-WIDTH (add1 (- max-depth this-depth)))]
    [(gen-tree (attributes p b-f b l cs) children)
     (apply + (cons 1 (for/list ([c children]) 
                        (calculate-width-for-depth c (add1 this-depth) max-depth))))]))

(define (calculate-width t)
  (calculate-width-for-depth t 0 (calculate-depth t)))

(define (calculate-depth tree)
  (define depth 0)
  (define (check-d d t)
    (match t
      [(gen-tree (attributes p b-f b l cs) '#())
       (when (> d depth) (set! depth d))]
      [(gen-tree (attributes p b-f b l cs) children)
       (for ([c children]) (check-d (add1 d) c))]))
  (check-d 1 tree)
  depth)

(define (calc-size t)
  (match t
    [(gen-tree (attributes p b-f b l cs) '#())
     1]
    [(gen-tree (attributes p b-f b l cs) children)
     (apply + (cons 1(for/list ([c children]) 
                (calc-size c))))]))
  
(define (basic-layout-tree t)
  (define max-depth (calculate-depth t))
  (define (layout-subtree t root-x root-y depth)
    (match t
      [(gen-tree (attributes p b-f b l cs) '#())
       (set-coords-x! cs root-x)
       (set-coords-y! cs root-y)]
      [(gen-tree (attributes p b-f b l cs) children)
       (define widths (for/list ([c children]) 
                        (calculate-width-for-depth c depth max-depth)))
       (define width (apply + widths))
       (define x (- root-x (/ width 2)))
       (for ([c children] [w widths])
         (layout-subtree c (+ x (/ w 2)) (+ root-y 1) (add1 depth))
         (set! x (+ x w)))
       (set-coords-x! cs root-x)
       (set-coords-y! cs root-y)]))
  (define w (calculate-width t))
  (layout-subtree t 0 1 1)
  w)

(define (layout-tree t)
  (basic-layout-tree t))
  
(define yscale-base .62)
(define (set-y-base f) (set! yscale-base f))
(define (ybase-sum) (/ yscale-base (- 1 yscale-base)))
(define (find-ybase-center)
  (define mid (/ (ybase-sum) 2))
  (define sums (for/hash ([i 10]) (values (abs (- mid
                                             (apply + (for/list ([k i]) 
                                                        (expt yscale-base i)))))
                                          i)))
  (hash-ref sums (apply min (hash-keys sums))))


(define trans-steps 15)
(define (set-t-s x) (set! trans-steps x))

(define Y-SHIFT 35)
(define (set-y-shift s) (set! Y-SHIFT s))

(define tree-frame%
  (class frame%
    
    (init t w h)
    (define tree t)
    (define width w)
    (define height h)
    (define shift (/ w 2))
    
    (define y-index 0)
    (define x-coord 0)
    (define scale 1)
    (define/private (rescale factor)
      (set! scale (* scale factor)))
    (define/private (trans-x x)
      (set! x-coord (+ x-coord x))#t)
    (define/private (shift-y steps)
      (set! y-index (+ y-index steps)))
    
    (define t-width (layout-tree tree))
    (define depth (calculate-depth tree))
    (define rescale-factor (/ w t-width))
    (define scale-factor (expt rescale-factor (/ 1 depth)))
    
    (super-new [label "Tree Browser"]
               [width w]
               [height h])
    
    (rescale rescale-factor)
    (define canvas (new canvas% [parent this]
                        [paint-callback (lambda (canvas dc)
                                          (draw-t))]))
                                          
    (define dc (send canvas get-dc))
    
    (define/public (display)
      (send this show #t))
    
    (define y-scale (/ h (ybase-sum)))
    (define y-cs (for/list ([y 10])
                   (* y-scale
                      (apply + (for/list ([i (in-range 1 y)]) (expt yscale-base i))))))
    (define/private (i-for-y y-raw)
      (define y (- y-raw Y-SHIFT))
      (define diffs (for/hash ([i 10] [y-c y-cs]) 
                      (values (+ 0.0 (abs (- y y-c))) i)))
      (hash-ref diffs (+ 0.0 (apply min (hash-keys diffs)))))
    
    (define/private (delta-y y)
      (define new-i (i-for-y y))
      (define old-i (find-ybase-center))
      (- old-i new-i))
    (define/private (delta-x x)
      (/ (- (/ width 2) x) scale))
    
    (define/override (on-subwindow-event receiver event)
      (if (send event button-down?)
          (let ([x (send event get-x)]
                [y (send event get-y)])
            (define ∆y (delta-y y))
            (define ∆x (delta-x x))
            (animate-transition ∆x ∆y))
          #f))
    
    (define/private (animate-transition ∆x ∆y)
      (define scaling (expt scale-factor ∆y))
      (define dx (/ ∆x trans-steps))
      (define dy (/ ∆y trans-steps))
      (define ds (expt scaling (/ 1 trans-steps)))
      (for ([i trans-steps])
        (trans-x dx)
        (shift-y dy)
        (rescale ds)
        (send canvas refresh-now
              (λ (dc) (draw-t)))))
    
    (define map-y-memo (make-hash))
    (define map-y-int-memo (make-hash))
    (define/private (map-y-int y)
      (hash-ref map-y-int-memo y
                (λ ()
                  (define res (if (< 0 y)
                                  (+ Y-SHIFT (* (apply + (for/list ([i (in-range 1 y)]) 
                                                      (expt yscale-base i)))
                                           y-scale))
                                  (- Y-SHIFT (* (+ (abs y) 1) y-scale))))
                  (hash-set! map-y-int-memo y res)
                  res)))
    (define/private (map-y y)
      (hash-ref map-y-memo y
                (λ ()
                  (define y-t (truncate y))
                  (define res (if (= y y-t)
                                  (map-y-int y)
                                  (let ([frac (abs (- y y-t))]
                                        [next (if (<= 0 y-t) (+ y-t 1) (- y-t 1))])
                                    (+ (* frac (map-y-int next))
                                       (* (- 1 frac) (map-y-int y-t))))))
                  (hash-set! map-y-memo y res)
                  res)))
    
    (define/private (adjust-x x)
      (* scale (+ x-coord x)))
    (define/private (adjust-y y)
      (+ y y-index))
    
    (define/private (line x1-raw y1-raw x2-raw y2-raw)
      (define x1 (adjust-x x1-raw))
      (define x2 (adjust-x x2-raw))
      (define y1 (adjust-y y1-raw))
      (define y2 (adjust-y y2-raw))
      (when (or (and (x1 . > . (- shift)) (x1 . < . shift) 
                     (y1 . > . -1) (y1 . < . 7))
                (and (x2 . > . (- shift)) (x2 . < . shift) 
                     (y2 . > . -1) (y2 . < . 7)))
        (send dc set-brush no-brush)
        (send dc set-pen red-pen)
        (send dc draw-line (+ shift x1) (map-y y1) (+ shift x2) (map-y y2))))
    
    (define/private (node x-raw y-raw)
      (define x (adjust-x x-raw))
      (define y (adjust-y y-raw))
      (when (and (x . > . (- shift)) (x . < . shift)
                 (y . < . 4) (y . > . -1))
        (send dc set-pen no-pen)
        (send dc set-brush blue-brush)
        (send dc draw-ellipse (+ shift (- x 5)) (- (map-y y) 5) 10 10)))
    
    (define/private (draw-t)
      (define (draw-subtree t d)
        (match t
          [(gen-tree (attributes p b-f b l (coords x y)) '#())
           (node x y)]
          [(gen-tree (attributes p b-f b l (coords x y)) children)
           (for ([c children])
             (match c 
               [(gen-tree (attributes p b-f b l (coords c-x c-y)) children)
                (line x y c-x c-y)
                (draw-subtree c (add1 d))]))
           (node x y)]))
      (send dc set-smoothing 'aligned)
      (draw-subtree tree 0))))

;;; end treeframe%
         
(define (show-trace trace)
  (define t (make-tree trace))
  (printf "~s nodes\n" (calc-size t))
  (define tf (new tree-frame% [t t] [w 700] [h 700]))
  (send tf display))

                     






