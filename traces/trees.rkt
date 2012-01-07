#lang racket

(require racket/math
         racket/draw
         racket/gui)

(provide show-trace)

;; tree browser prototype
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

(define SCROLL-RANGE 10000)

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

;; layout for a trace
;; need max depth - get from locs
;; need max width for each loc
;; pre-layout - make list of subtrees for each loc
;; take max in layout
;; find nearest point to click - do reverse transforms
;;     then search down tree by x until the right y

(define (max-depth trace)
  (define max-d 0)
  (let loop ([t trace])
    (match t
      [`((,loc ,other-stuff ...) ,remaining-traces ...)
       (when (> (add1 (length loc)) max-d)
         (set! max-d (add1 (length loc))))
       (loop remaining-traces)]
      [else max-d])))

(define trace-state%
  (class object%
    
    (init trace-init)
    
    (define step 0)
    (define tree (vector 0))
    (define trace trace-init)
    (define final-tree (make-tree trace))
    (define width (calculate-width final-tree))
    (define depth (calculate-depth final-tree))
    (define last-atts #f)
    
    (super-new)
    
    (update-tree-one-step)
    
    (define/public (take-step)
      (unless (equal? step (sub1 (length trace)))
        (set! step (add1 step))
        (update-tree-one-step)))
    
    (define/public (get-tree) tree)
    
    (define/public (get-width) width)
    (define/public (get-depth) depth)
    
    (define/public (current-atts)
      last-atts)
    
    (define/private (update-tree-one-step)
      (define trace-step (list-ref trace step))
      (match trace-step
        [`(,loc ,name ,state ,term ,body ,bound ,depth)
         (define atts (attributes name (gensym) (positive? bound) term (coords #f #f)))
         (set! last-atts atts)
         (set! tree (insert-tree-node loc atts tree))]
        [else (error "Trace had incorrect format, failed to update tree")])
      ;(set! width (calculate-width tree))
      ;(set! depth (calculate-depth tree))
      (layout-tree tree))))
      

  
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

(define tree-canvas%
  (class canvas%
    
    (super-new)
    
    (define scroll-handler (λ (e) #f))
    (define/public (set-scroll-handler f)
      (set! scroll-handler f))
    (define/override (on-scroll event)
      (scroll-handler event))
    
    (define key-handler (λ (e) #f))
    (define/public (set-key-handler f)
      (set! key-handler f))
    (define/override (on-char event)
      (key-handler event))))

(define tree-frame%
  (class frame%
    
    (init t w h)
    (define trace (new trace-state% [trace-init t]))
    (define width w)
    (define height h)
    (define shift (/ w 2))
    
    (super-new [label "Tree Browser"])
    
    (define (t-width)
      (send trace get-width))
    (define (depth)
      (send trace get-depth))
    
    (define y-index 0)
    (define x-coord 0)
    (define scale 1)
    (define/private (rescale factor)
      (set! scale (* scale factor)))
    (define/private (trans-x x)
      (set! x-coord (+ x-coord x))
      (update-scroll-x x-coord))
    (define/private (shift-y steps)
      (set! y-index (+ y-index steps))
      (update-scroll-y y-index))
    
    (define rescale-factor (/ w (t-width)))
    (define scale-factor (expt rescale-factor (/ 1 (depth))))
    
    (rescale rescale-factor)
    (define canvas (new tree-canvas% [parent this]
                        [min-width w]
                        [min-height h]
                        [style (list 'hscroll 'vscroll)]
                        [paint-callback (lambda (canvas dc)
                                          (draw-t))]))
    (send canvas set-scroll-range 'horizontal SCROLL-RANGE)
    (send canvas set-scroll-range 'vertical SCROLL-RANGE)
    (send canvas set-scroll-pos 'vertical 0)
    (send canvas set-scroll-pos 'horizontal (/ SCROLL-RANGE 2))
    
    (send canvas set-scroll-handler
          (λ (event)
            (define dir (send event get-direction))
            (define pos (update-scroll-pos event))
            (define x-pos x-coord)
            (define y-pos y-index)
            (match dir
              ['horizontal
               (set! x-pos (* (t-width) (- .5 (/ pos SCROLL-RANGE))))]
              ['vertical
               (set! y-pos (- (* (depth) (/ pos SCROLL-RANGE))))])
            (animate-transition (- x-pos x-coord) (- y-pos y-index))))
    
    (send canvas set-key-handler
          (λ (event)
            (define d-y 0)
            (define d-x 0)
            (match (send event get-key-code)
              ['wheel-down
               (set! d-y (- (/ (depth) 40)))]
              ['wheel-up
               (set! d-y (/ (depth) 40))]
              ['wheel-right
               (set! d-x (- (/ (t-width) 40)))]
              ['wheel-left
               (set! d-x (/ (t-width) 40))])
            (animate-transition d-x d-y)))
    
    (define/private (update-scroll-pos event)
      (define pos (send event get-position))
      (match (send event get-event-type)
        ['line-up
         (- pos (/ SCROLL-RANGE 20))]
        ['line-down
         (+ pos (/ SCROLL-RANGE 20))]
        ['page-up
         (- pos (/ SCROLL-RANGE 20))]
        ['page-down
         (+ pos (/ SCROLL-RANGE 20))]
        [else pos]))
    
    (define/private (update-scroll-x x)
      (send canvas set-scroll-pos 'horizontal (+ (* (- x) (/ SCROLL-RANGE (t-width))) 
                                                 (/ SCROLL-RANGE 2))))
    (define/private (update-scroll-y y-index)
      (send canvas set-scroll-pos 'vertical (* (/ y-index (- (depth))) SCROLL-RANGE)))
                                          
    (define dc (send canvas get-dc))
    
    (define/public (display)
      (send this show #t))
    
    (define panel1 (new vertical-panel% [parent this]
                             [min-height 80]
                             [stretchable-height 80]))
    (define panel2 (new horizontal-panel% [parent panel1]
                             [min-height 40]
                             [stretchable-height 40]))
    (define step-button (new button% [parent panel2]
                             [label "Step"]
                             [callback (λ (b e) (step-redraw))]))
    (define rule-message (new text-field% [parent panel2]
                              [label "Rule:"]))
    (define term-message (new text-field% [parent panel1]
                              [label "Term:"]))
    (update-messages)
    
    (define/private (step-redraw)
      (send trace take-step)
      (send canvas refresh-now
              (λ (dc) (draw-t)))
      (update-messages))
    
    (define/private (update-messages [atts #f])
      (define as (if atts atts (send trace current-atts)))
      (match as
        [(attributes name id bound term coords)
         (send rule-message set-value (format "~s" name))
         (send term-message set-value (format "~s" term))]))
    
    
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
    
;    (define/override (on-subwindow-event receiver event)
;      (if (send event button-down?)
;          (let ([x (send event get-x)]
;                [y (send event get-y)])
;            (define ∆y (delta-y y))
;            (define ∆x (delta-x x))
;            (animate-transition ∆x ∆y))
;          #f))
    
    (define/private (animate-transition ∆x ∆y)
      (define scaling (expt scale-factor ∆y))
      (define trans-steps (inexact->exact (ceiling (max (abs (/ (* ∆x 40) (t-width)))
                                                        (abs (/ (* ∆y 40) (depth)))))))
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
      (draw-subtree (send trace get-tree) 0))))

;;; end treeframe%
         
(define (show-trace trace)
  (define tf (new tree-frame% [t trace] [w 700] [h 700]))
  (send tf display))

                     






