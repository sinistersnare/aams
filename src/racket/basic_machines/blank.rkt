#lang racket

; just gonna use this as a template for all the machines.
; TODO: make this some sort of interface. Does racket have interfaces? What would be idiomatic?
;       Would probably make State an interface itself, or some object that can be
;       different to each machine. And then destructure it in the match,
;       instead of having different args for each step function.

; create an initial state around a closed expression
(define (inj-TYPE e) '())
; move the machine 1 step from a given state.
(define (step-TYPE exp env store cont) '())
; evaluate from an initial state
(define (evaluate e)
  (define (is-fixed st)
    (match st
      ; if the control is an abstraction and the kont is mt, then we are at a fixed point.
      ; CHANGE THIS PART TO BE THE FIXED-POINT!
      [`((λ ,x ,e) ,env ,store mt) #t]
      [else #f]))
  (define (go st)
    (define next-st (apply step-TYPE st))
    (println `(next-state: ,next-st))
    (if (is-fixed next-st) next-st (go next-st)))
  (go (inj-TYPE e)))