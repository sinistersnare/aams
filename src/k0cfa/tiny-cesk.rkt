#lang racket

(require (only-in racket/hash hash-union))

; this is a CESK* machine, with a globalized store.
; it implements some basic scheme features like 'if', 'let',
; and multi argument functions. Also has numbers and booleans.

(struct state (ctrl env nextkaddr) #:transparent)

(struct closure (lam env) #:transparent)
(struct prim (op) #:transparent)

(struct ifk (et ef env nextkaddr) #:transparent)
(struct letk (x body env nexkaddr) #:transparent)
(struct appk (done todo env nextkaddr) #:transparent)

(define prims
  (hash '+ (prim +)
        'equal? (prim equal?)
        'number? (prim number?)
        'boolean? (prim boolean?)))

(define (lambda? e)
  (match e
    ; only standard multiarg lambda for now
    [`(λ (,_ ...) ,_) #t] ; standard multiarg lambda
    [`(λ ,(? symbol?) ,_) #f] ; dont allow varag lambda
    [else #f]))

; checks a syntactic expression to see if its an atomically evaluable expression
(define (atomic? v)
  (match v
    [(or (? symbol?) (? lambda?)
         (? number?) (? boolean?)) #t]
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

(define (atomic-eval st)
  (match-define (state ctrl env kont) st)
  (match ctrl
    ; wrap lambdas into a closure
    [(? lambda?) (closure ctrl env)]
    ; no evaluation needed for these
    [(or (? boolean?) (? number?)) ctrl] 
    ; lookup symbol to evaluate
    [(? symbol?) (get-from-store (hash-ref env ctrl))]))

(define (step-atomic st)
  (match-define (state ctrl env a) st)
  (define v (atomic-eval st))
  (define k (get-from-store a))
  (match k
    ['mt st]
    [(ifk et ef envprime c) #:when (equal? v #f)
                            (state ef envprime c)]
    [(ifk et ef envprime c) #:when (not (equal? v #f))
                            (state et envprime c)]
    [(letk x eb envprime c)
     (define b (add-to-store! v st))
     (state eb (hash-set envprime x b) c)]
    [(appk done (cons eh et) envprime c)
     (define b (add-to-store! (appk (append done (list v)) et envprime c) st))
     (state eh envprime b)]
    [(appk (cons (prim op) vs) '() envprime c)
     (define vprime (apply op (append vs (list v))))
     (state vprime envprime c)]
    [(appk (cons (closure `(λ (,xs ...) ,eb) lamenv) incomplete-vs) '() envprime c)
     (define vs (append incomplete-vs (list v)))
     (define bs (map (λ (v) (add-to-store! v st)) vs))
     (define new-bindings (make-immutable-hash (map cons xs bs)))
     (define extended-lamenv (hash-union lamenv new-bindings #:combine (λ (a b) b)))
     (state eb extended-lamenv c)]))

(define (step st)
  (match-define (state ctrl env a) st)
  #;(displayln `(st ,store))
  (match ctrl
    [(? atomic? ctrl) (step-atomic st)]
    [`(if ,ec ,et ,ef)
     (define b (add-to-store! (ifk et ef env a) st))
     (state ec env b)]
    [`(let (,x ,ex) ,ebody)
     (define b (add-to-store! (letk x ebody env a) st))
     (state ex env b)]
    [`(prim ,op ,e0 ,es ...)
     (define b (add-to-store! (appk (list (hash-ref prims op)) es env a) st))
     (state e0 env b)]
    [`(,ef ,es ...)
     (define b (add-to-store! (appk '() es env a) st))
     (state ef env b)]))


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
    (if (fix? nextst st) (cons (atomic-eval st) st) (run nextst)))
  (run state0))

(define e evaluate)










