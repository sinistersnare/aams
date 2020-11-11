#lang racket

(require (only-in racket/hash hash-union))

; this is a CESK* machine, with a globalized store.
; it implements some basic scheme features like 'if', 'let',
; and multi argument functions. Also has numbers and booleans.

(struct prim (op) #:transparent)
(struct state (ctrl env nextkaddr) #:transparent)

(struct iff (et ef env nextkaddr) #:transparent)
(struct letf (x body env nexkaddr) #:transparent)
(struct appf (done todo env nextkaddr) #:transparent)

(define (atomic? v)
  (match v
    [(prim _) #t]
    [`(λ (,_ ...) ,_) #t]
    [(? number?) #t]
    [(? boolean?) #t]
    [else #f]))

(define prims
  (hash
   '+ (prim (λ vs (foldl (λ (x accum) (if (number? x) (+ x accum) (raise 'not-a-number))) 0 vs)))
   'unsafe+ (prim +)))

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
  (match-define (state ctrl env kaddr) st)
  (define k (get-from-store kaddr))
  ; ctrl should be atomic here
  (match k
    ['mt st]
    [(appf (cons (prim op) vs) '() envprime nextkaddr)
     (define full-vs (append vs (list ctrl)))
     (define result (apply op full-vs))
     (state result envprime nextkaddr)]
    [(appf (cons `(λ (,xs ...) ,body) vs) '() envprime nextkaddr)
     (define bs (map (λ (v) (add-to-store! (cons v env) st)) (append vs (list ctrl))))
     (define new-env-mappings (map cons xs bs))
     (define new-env (hash-union envprime (make-immutable-hash new-env-mappings)))
     (state body new-env nextkaddr)]
    [(appf done (cons head rest) envprime nextkaddr)
     (define nextk (appf (append done (list ctrl)) rest envprime nextkaddr))
     (define b (add-to-store! nextk st))
     (state head envprime b)]
    [(iff et ef envprime nextkaddr)
     (if (equal? ctrl #f)
         (state ef envprime nextkaddr)
         (state et envprime nextkaddr))]
    [(letf x body envprime nextkaddr)
     (define b (add-to-store! (cons ctrl env) st))
     (state body (hash-set envprime x b) nextkaddr)]))

(define (step st)
  (match-define (state ctrl env kaddr) st)
  ;#;(displayln st) #;(displayln store) #;(newline)
  (match ctrl
    [(? atomic?) (step-atomic st)]
    [`(if ,ec ,et ,ef)
     (define nextk (iff et ef env kaddr))
     (define b (add-to-store! nextk st))
     (state ec env b)]
    [`(let (,x ,e) ,body)
     (define nextk (letf x body env kaddr))
     (define b (add-to-store! nextk st))
     (state e env b)]
    [`(,ef ,es ...)
     (define nextk (appf '() es env kaddr))
     (define b (add-to-store! nextk st))
     (state ef env b)]
    [(? symbol?)
     (define not-found (gensym))
     (define addr (hash-ref env ctrl not-found))
     (if (equal? addr not-found)
         (if (hash-has-key? prims ctrl)
             (state (hash-ref prims ctrl) env kaddr)
             (raise `(variable-not-in-scope: ,ctrl)))
         (match-let ([(cons v venv) (get-from-store (hash-ref env ctrl))])
           (state v venv kaddr)))]))


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













