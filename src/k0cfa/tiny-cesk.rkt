#lang racket

(require (only-in racket/hash hash-union))

; this is a CESK* machine, with a globalized store.
; it implements some basic scheme features like 'if', 'let',
; and multi argument functions. Also has numbers and booleans.

;
; eval and apply states
;
; eval will evaluate expressions
; apply will apply values to produce the next state.
(struct E (sexpr env nextkaddr time) #:transparent)
(struct A (val env nextkaddr time) #:transparent)

(struct addr (n) #:transparent)
(struct time (t) #:transparent)
(struct closure (lam env) #:transparent)
(struct quoteobj (sexpr) #:transparent)
(struct prim (op) #:transparent)

(struct mtk () #:transparent)
(struct ifk (et ef env a) #:transparent)
(struct callcck (a) #:transparent)
(struct setk (x env a) #:transparent)
(struct appappk (mval e env a) #:transparent)
(struct appk (done todo env a) #:transparent)
(struct appprimk (op env a) #:transparent)
(struct primk (op done todo env a) #:transparent)
(struct letk (vars done todo e env a) #:transparent)

(define (continuation-frame? v)
  (match v
    [(or (? mtk?) (? ifk?) (? callcck?) (? setk?) (? appappk?)
         (? appk?) (? appprimk?) (? primk?) (? letk?)) #t]
    [else #f]))

(define prims
  (hash '+ (prim +)
        'equal? (prim equal?)
        'number? (prim number?)
        'boolean? (prim boolean?)
        'continuation? (prim continuation-frame?)
        'cons (prim cons) 'car (prim car) 'cdr (prim cdr)))

(define (lambda? e)
  (match e
    [`(λ (,_ ...) ,_) #t] ; standard multiarg lambda
    [`(λ ,(? symbol?) ,_) #t] ; varag lambda
    [else #f]))

; checks a syntactic expression to see if its an atomically evaluable expression
(define (atomic? v)
  (match v
    [(or (? symbol?) (? lambda?)
         (? number?) (? boolean?)
         `(quote ,_)) #t]
    [else #f]))

; global store, default value contains the mt kont.
(define store (make-hash (list (cons (addr 0) (mtk)))))
; adds a value to the store, returns the address of that value.
(define (add-to-store! a v)
  (hash-set! store a v))
(define (get-from-store a)
  (hash-ref store a))
(define (reset-store!)
  (set! store (make-hash (list (cons (addr 0) (mtk))))))


(define (alloc st offset)
  (match st
    [(E _ _ _ (time t)) (addr (+ t offset))]
    [(A _ _ _ (time t)) (addr (+ t offset))]))

(define (tick st amt)
  (match st
    [(E _ _ _ (time t)) (time (+ t amt))]
    [(A _ _ _ (time t)) (time (+ t amt))]))

(define (eval-step st)
  (match-define (E sexpr p a t) st)
  ; evalutes atomic expressions so they can be applied.
  ; call only when (atomic? sexpr).
  (define (atomic-eval)
    (match sexpr
      [(? lambda?) (closure sexpr p)]
      [`(quote ,e) (quoteobj e)]
      [(or (? number?) (? boolean?)) sexpr]
      [(? symbol?) (get-from-store (hash-ref p sexpr))]))
  ; actual transitions
  (match sexpr
    [(? atomic?)
     (define v (atomic-eval))
     (A v p a t)]
    [`(if ,ec ,et ,ef)
     (define b (alloc st 0))
     (define u (tick st 1))
     (add-to-store! b (ifk et ef p a))
     (E ec p b u)]
    [`(let () e)
     (define u (tick st 1))
     (E e p a u)]
    [`(let ([,x0 ,e0] [,xs ,es] ...) ,eb)
     (define b (alloc st 0))
     (define u (tick st 1))
     (add-to-store! b (letk (cons x0 xs) '() es eb p a))
     (E e0 p b u)]
    [`(call/cc e)
     (define b (alloc st 0))
     (define u (tick st 1))
     (add-to-store! b (callcck a))
     (E e p b u)]
    [`(set! ,x ,e)
     (define b (alloc st 0))
     (define u (tick st 1))
     (add-to-store! b (setk x a))
     (E e p b u)]
    [`(prim ,op)
     (match-define (prim pf) (hash-ref prims op))
     (define v (apply pf '()))
     (A v p a t)]
    [`(prim ,op ,e0 ,es ...)
     (define b (alloc st 0))
     (define u (tick st 1))
     (add-to-store! b (primk (hash-ref prims op) '() es p a))
     (E e0 p b u)]
    [`(apply-prim ,op ,e)
     (define b (alloc st 0))
     (define u (tick st 1))
     (add-to-store! b (appprimk (hash-ref prims op) a))
     (E e p b u)]
    [`(apply ,ef ,ex)
     (define b (alloc st 0))
     (define u (tick st 1))
     (add-to-store! b (appappk '() ex p a))
     (E ef p b u)]
    [`(,ef ,es ...)
     (define b (alloc st 0))
     (define u (tick st 1))
     (add-to-store! b (appk '() es p a))
     (E ef p b u)]))

(define (apply-step st)
  (match-define (A v p a t) st)
  (define k (get-from-store a))
  (match k
    [(mtk) st]
    [(ifk et ef p c)
     #:when (equal? v #f)
     (E ef p c t)]
    [(ifk et ef p c)
     #:when (not (equal? v #f))
     (E et p c t)]
    [(letk vars done '() eb pk c)
     (define bs (map (λ (i) (alloc st i)) (range (length vars))))
     (define u (tick st (length vars)))
     (define doneprime (append done (list v)))
     (define pkprime
       (foldl (λ (k v res) (hash-set res k v)) pk vars bs))
     (foldl (λ (k v _) (add-to-store! k v)) (void) bs doneprime)
     (E eb pkprime c u)]
    [(letk vars done (cons eh et) eb pk c)
     (define b (alloc st 0))
     (define u (tick st 1))
     (add-to-store! b (letk vars (append done (list v)) et eb pk c))
     (E eh pk b u)]
    [(callcck c)
     #:when (lambda? v)
     (match-define (closure `(λ (,x) ,e) plam) v)
     (define plamprime (hash-set plam x c))
        (E e plamprime c t)]
    [(callcck c)
     #:when (continuation-frame? v)
     (raise 'idk-whats-going-on-here!)]
    [(setk x pk c)
     (add-to-store! (hash-ref pk x) v)
     (A (void) pk c t)]
    [(appprimk (prim op) pk c)
     (define vprime (apply op v))
     (A vprime pk c t)]
    [(primk (prim op) done '() pk c)
     (define vprime (apply op (append done (list v))))
     (A vprime pk c t)]
    [(primk op done (cons eh et) pk c)
     (define b (alloc st 0))
     (define u (tick st 1))
     (add-to-store! b (primk op (append done (list v)) et pk c))
     (E eh pk b u)]
    [(appappk '() e pk  c)
     (define b (alloc st 0))
     (define u (tick st 1))
     (add-to-store! b (appappk v e pk c))
     (E e pk b u)]
    [(appappk (closure `(λ (,xs ...) ,eb) plam) _ _ c)
     (define bs (map (λ (i) (alloc st i)) (range (length xs))))
     (define u (tick st (length xs)))
     (define plamprime (foldl (λ (k v res) (hash-set res k v)) plam xs bs))
     (foldl (λ (k v _) (add-to-store! k v)) (void) bs v)
     (E eb plamprime c u)]
    [(appappk (closure `(λ ,x ,eb) plam) _ _ c)
     (define b (alloc st 0))
     (define u (tick st 1))
     (define plamprime (hash-set plam x b))
     (add-to-store! b v)
     (E eb plamprime)]
    [(appk (cons (closure `(λ (,xs ...) ,eb) plam)  vs) '() pk c)
     (define bs (map (λ (i) (alloc st i)) (range (length xs))))
     (define u (tick st (length xs)))
     (define plamprime (foldl (λ (k v res) (hash-set res k v)) plam xs bs))
     (define vsprime (append vs (list v)))
     (foldl (λ (k v _) (add-to-store! k v)) (void) bs vsprime)
     (E eb plamprime c u)]
    [(appk (cons (closure `(λ ,x ,eb) plam) vs) '() pk c)
     (define b (alloc st 0))
     (define u (tick st 1))
     (define plamprime (hash-set plam x b))
     (define vsprime (append vs (list v)))
     (add-to-store! b vsprime)
     (E eb plamprime c u)]
    [(appk (list (? continuation-frame? klam)) '() pk c)
     (define b (alloc st 0))
     (define u (tick st 1))
     (add-to-store! b klam)
     (A v pk b u)]
    [(appk done (cons eh et) pk c)
     (define b (alloc st 0))
     (define u (tick st 1))
     (add-to-store! b (appk (append done (list v)) et pk c))
     (E eh pk b u)]))


; forms an initial state from an expression
(define (inject e) (E e (hash) (addr 0) (time 1)))

(define (fix? st0 st1)
  (equal? st0 st1))

; iterates an initial state until fixpoint
(define (evaluate prog)
  (reset-store!)
  (define state0 (inject prog))
  (define states (cons state0 '()))
  (define (run st)
    (define nextst (match st
                     [(E _ _ _ _) (eval-step st)]
                     [(A _ _ _ _) (apply-step st)]))
    (set! states (cons nextst states))
    (if (fix? nextst st) st (run nextst)))
  (run state0))

(define e evaluate)










