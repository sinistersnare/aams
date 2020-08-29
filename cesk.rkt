#lang racket


; create an initial state around a closed expression
(define (inj-cesk e) (list e (hash) (hash) 'mt))

; move the machine 1 step from a given state.
(define (step-cesk exp env store cont)
  (match exp
    [(? symbol? x)
     (match-define `(,v ,pprime) (hash-ref
                                  store
                                  (hash-ref env x (lambda () (raise `(not found in env ,x ,env))))
                                  (lambda () (raise `(not found in store ,x ,store)))))
     (list v pprime store cont)]
    [`(,e0 ,e1)
     (list e0 env store `(ar ,e1  ,env ,cont))]
    [`(λ ,(? symbol? xvar) ,ebody)
     (match cont
       ['mt (list exp env store cont)]
       [`(ar ,e ,pprime ,k)
        (list e pprime store `(fn ,exp ,env ,k))]
       [`(fn (λ ,(? symbol? x) ,e) ,pprime ,k)
        ; gensym so we get a fresh symbol, so no collisions.
        (define newaddr (gensym 'a))
        (list e (hash-set pprime x newaddr) (hash-set store newaddr (list exp env)) k)]
       [else (raise `(bad-continuation! ,cont))])]
    [else (raise `(bad-syntax! ,exp ,env ,store ,cont))]))

; evaluate from an initial state
(define (evaluate e)
  (define (is-fixed st)
    (match st
      ; if the control is an abstraction and the kont is mt, then we are at a fixed point.
      [`((λ ,x ,e) ,env ,store mt) #t]
      [else #f]))
  (define (go st)
    (define next-st (apply step-cesk st))
    (println `(next-state: ,next-st))
    (if (is-fixed next-st) next-st (go next-st)))
  (go (inj-cesk e)))