#lang racket

; create an initial state around a closed expression
(define (inj-ceskt* e)
  ; I made timestamp start at 1 because 0 is used by the mt continuation.
  ; TODO: Am I wrong to do this? Is this bad?
  (list e (hash) (hash 0 'mt) 0 1))

; move the machine 1 step from a given state.
(define (step-ceskt* exp env store cont timestamp)
  (define tick add1)
  (define alloc-addr timestamp)
  (match exp
    [(? symbol? x)
     (match-define `(,v ,pprime)
       (hash-ref store (hash-ref env x (lambda () (raise `(not-found-in-env ,x ,env))))
                 (lambda () (raise `(not-found-in-store ,x ,store)))))
     (list v pprime store cont (tick timestamp))]
    [`(,e0 ,e1)
     (list e0 env (hash-set store alloc-addr `(ar ,e1 ,env ,cont)) alloc-addr (tick timestamp))]
    [`(λ ,xarg ,ebody)
     (match (hash-ref store cont (lambda () (raise `(cant-find-cont 'cont ,store))))
       [`(ar ,e ,pprime ,c)
        (list e pprime (hash-set store alloc-addr `(fn ,exp ,env ,c)) alloc-addr (tick timestamp))]
       [`(fn (λ ,x ,e) ,pprime ,c)
        (list e (hash-set pprime x alloc-addr)
              (hash-set store alloc-addr (list exp env)) c (tick timestamp))]
       [else (raise `(bad-cont ,cont ,store))])]
    [else (raise `(bad-syntax ,exp ,env ,store ,cont ,timestamp))]))

; evaluate from an initial state
(define (evaluate e)
  (define (is-fixed st)
    (match st
      ; if the control is an abstraction and the kont is mt, then we are at a fixed point.
      ; k = 0 is the first thing we allocate, the mt continuation.
      [`((λ ,x ,e) ,env ,store ,k ,timestamp) (= k 0)]
      [else #f]))
  (define (go st)
    (define next-st (apply step-ceskt* st))
    (println `(next-state: ,next-st))
    (if (is-fixed next-st) next-st (go next-st)))
  (go (inj-ceskt* e)))