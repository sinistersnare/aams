#lang racket

; just gonna use this as a template for all the machines.

; create an initial state around a closed expression
(define (inj-cesk e) '())
; move the machine 1 step from a given state.
(define (step-cesk exp env store cont) '())
; evaluate from an initial state
(define (evaluate e)
  (define (is-fixed st)
    (match st
      ; if the control is an abstraction and the kont is mt, then we are at a fixed point.
      ; CHANGE THIS PART TO BE THE FIXED-POINT!
      [`((λ ,x ,e) ,env ,store mt) #t]
      [else #f]))
  (define (go st)
    (define next-st (apply step-cesk st))
    (println `(next-state: ,next-st))
    (if (is-fixed next-st) next-st (go next-st)))
  (go (inj-cesk e)))