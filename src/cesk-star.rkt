#lang racket

; create an initial state around a closed expression
(define (inj-cesk* e)
  (define first-k-addr (gensym 'ka))
  (list e (hash) (hash first-k-addr 'mt) first-k-addr))

; move the machine 1 step from a given state.
(define (step-cesk* exp env store cont)
  (match exp
    [(? symbol? x)
     (match-define `(,v ,pprime)
       (hash-ref store (hash-ref env x (lambda () (raise `(not-found-in-env ,x ,env))))
                 (lambda () (raise `(not-found-in-store ,x ,store)))))
     (list v pprime store cont)]
    [`(,e0 ,e1)
     (define new-k-addr (gensym 'ka))
     (list e0 env (hash-set store new-k-addr `(ar ,e1 ,env ,cont)) new-k-addr)]
    [`(λ ,(? symbol? xvar) ,ebody)
     (match (hash-ref store cont (lambda () (raise `(cont-not-found ,cont ,store))))
       ['mt (list exp env store cont)]
       [`(ar ,e ,pprime ,c)
        (define new-k-addr (gensym 'ka))
        (list e pprime (hash-set store new-k-addr `(fn ,exp ,env ,c)) new-k-addr)]
       [`(fn (λ ,(? symbol? x) ,e) ,pprime ,c)
        (define new-binding (gensym 'a))
        (list e (hash-set pprime x new-binding) (hash-set store new-binding (list exp env)) c)]
       [else (raise `(bad-cont! ,exp ,env ,store ,cont))])]
    [else (raise `(bad-syntax! ,exp ,env ,store ,cont))]))

; evaluate from an initial state
(define (evaluate e)
  (define (is-fixed st)
    (match st
      ; if the control is an abstraction and the kont is mt, then we are at a fixed point.
      [`((λ ,x ,e) ,env ,store ,kaddr) (equal? (hash-ref store kaddr (lambda () (raise 'noaddr)))
                                               'mt)]
      [else #f]))
  (define (go st)
    (define next-st (apply step-cesk* st))
    (println `(next-state: ,next-st))
    (if (is-fixed next-st) next-st (go next-st)))
  (go (inj-cesk* e)))