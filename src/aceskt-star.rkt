#lang racket

(require (only-in racket/random random-ref))

; create an initial state around a closed expression
; TODO: what does this look like in the abstract?
(define (inj-aceskt* e) '())

; move the machine 1 step from a given state.
(define (step-aceskt* exp env store cont timestamp)
  (define (tick t k) (add1 t))
  (match exp
    [(? symbol? x)
     (match-define `(,v ,pprime)
       ; randomly choose a value from the set of values in that addr
       ; TODO: this is what the paper wants right?
       (random-ref 
        (hash-ref store (hash-ref env x (lambda () (raise `(not-found-in-env ,x ,env))))
                  (lambda () (raise `(not-found-in-store ,x ,store))))))
     ; TODO: is this how a k should be found?
     (define k (random-ref (hash-ref store cont
                                     (lambda () (raise `(nothing-found-there ,store ,cont))))))
     (list v pprime store cont (tick timestamp k))]
    [`(,e0 ,e1)
     ; TODO: same here as above k.
     (define k (random-ref (hash-ref store cont
                                     (lambda () (raise `(nothing-found-there ,store ,cont))))))
     (list e0 env #;(TODO! hash adding) #;(TODO: alloc!) (tick timestamp k))]
    [`(λ ,xvar ,ebody) '()]
    [else (raise `(bad-syntax: ,exp ,env ,store ,cont))]))

; evaluate from an initial state
(define (evaluate e)
  (define (is-fixed st)
    (match st
      ; if the control is an abstraction and the kont is mt, then we are at a fixed point.
      ; TODO: CHANGE THIS PART TO BE THE FIXED-POINT!
      [`((λ ,x ,e) ,env ,store ,kaddr ,timestamp) #t]
      [else #f]))
  (define (go st)
    (define next-st (apply step-aceskt* st))
    (println `(next-state: ,next-st))
    (if (is-fixed next-st) next-st (go next-st)))
  (go (inj-aceskt* e)))