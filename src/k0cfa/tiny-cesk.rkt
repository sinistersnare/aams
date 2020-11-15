#lang racket

(require (only-in racket/hash hash-union))

; this is a CESK* machine, with a globalized store.
; it implements some basic scheme features like 'if', 'let',
; and multi argument functions. Also has numbers and booleans.

(struct state (ctrl env nextkaddr) #:transparent)

(struct closure (lambda env) #:transparent)
(struct prim (op) #:transparent)

(struct ifk (et ef env nextkaddr) #:transparent)
(struct letk (x body env nexkaddr) #:transparent)
(struct appk (done todo env nextkaddr) #:transparent)

(define prims
  (hash '+ (prim +)))

(define (atomic? v)
  (match v
    [(closure _ _) #t]
    [(? number?) #t]
    [(? boolean?) #t]
    [else #f]))

; The state is unneeded for now, just need an unused address
(define objcount 0)
(define (alloc st)
  (define addr (string->symbol (string-append "addr" (number->string objcount))))
  (set! objcount (add1 objcount))
  addr)

; global store, default value contains the mt kont.
(define store (make-hash (list (cons 'mt 'mt))))
; adds a value to the store, returns the address of that value.
(define (add-to-store! v st)
  (define addr (alloc st))
  (hash-set! store addr v)
  addr)
(define (get-from-store addr)
  (hash-ref store addr))
(define (reset-store!)
  (set! store (make-hash (list (cons 'mt 'mt)))))

(define (step-atomic st)
  (match-define (state ctrl env a) st)
  (match (get-from-store a)
    ['mt st]
    [(ifk et ef envprime c)
     (if (equal? ctrl #f)
         (state ef envprime c)
         (state et envprime c))]
    [(letk x eb envprime c)
     (define b (add-to-store! ctrl st))
     (state eb (hash-set envprime x b) c)]
    [(appk (cons (prim op) vs) '() envprime c)
     (state (apply op (append vs (list ctrl))) envprime c)]
    [(appk (cons (closure `(λ (,xs ...) ,eb) cloenv) vs) '() envprime c)
     (define bs (map (λ (v) (add-to-store! v st)) (append vs (list ctrl))))
     (define new-env-mappings (map cons xs bs))
     (state eb (hash-union cloenv (make-immutable-hash new-env-mappings)) c)]
    [(appk done (cons h t) envprime c)
     (define b (add-to-store! (appk (append done (list ctrl)) t envprime c) st))
     (state h envprime b)]))

(define (step st)
  (match-define (state ctrl env a) st)
  ; (displayln `(st: ,st))
  (match ctrl
    [(? atomic?) (step-atomic st)]
    [`(λ (,xs ...) ,body)
     (state (closure ctrl env) env a)]
    [`(if ,ec ,et ,ef)
     (define b (add-to-store! (ifk et ef env a) st))
     (state ec env b)]
    [`(let (,x ,ex) ,eb)
     (define b (add-to-store! (letk x eb env a) st))
     (state ex env b)]
    [`(prim ,op ,e0 ,es ...)
     (define b (add-to-store! (appk (list (hash-ref prims op)) es env a) st))
     (state e0 env b)]
    [`(,ef ,es ...)
     (define b (add-to-store! (appk '() es env a) st))
     (state ef env b)]
    [(? symbol?)
     (define v (get-from-store (hash-ref env ctrl)))
     (state v env a)]))


; forms an initial state from an expression
(define (inject e) (state e (hash) 'mt))

(define (fix? st0 st1)
  (match-define (state c0 _ k0) st0)
  (match-define (state c1 _ k1) st1)
  (and (eq? k0 'mt) (eq? k1 'mt) (eq? c0 c1)))

; iterates an initial state until fixpoint
(define (evaluate prog)
  (reset-store!)
  (define state0 (inject prog))
  (define (run st)
    (define nextst (step st))
    (if (fix? nextst st) st (run nextst)))
  (run state0))

(define e evaluate)













