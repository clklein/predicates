#lang racket

(require "red-tests.rkt")

(define (main)
  (command-line
   #:once-each
   [("-s" "--size") size "Size bound for generation"
                       (gen-indef (string->number size))]))

(main)