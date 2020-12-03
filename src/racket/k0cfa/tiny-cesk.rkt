#lang racket

; this is a time-stamped CESK* machine, with a globalized store.
; it implements some basic scheme features like 'if', 'let',
; and multi argument functions. Also has numbers and booleans.

; eval and apply states
;
; eval will evaluate expressions
; apply will apply values to produce the next state.
(struct E (sexpr env store kstore nextkaddr time) #:transparent)
(struct A (val store kstore nextkaddr time) #:transparent)

(struct addr (n) #:transparent)
(struct time (t) #:transparent)
(struct closure (lam env) #:transparent)
(struct quoteobj (sexpr) #:transparent)
(struct prim (op) #:transparent)

(struct ktype () #:transparent) ; super-type for continuation frames
(struct mtk ktype () #:transparent)
(struct ifk ktype (et ef env kaddr) #:transparent)
(struct callcck ktype (kaddr) #:transparent)
(struct setk ktype (a kaddr) #:transparent)
(struct appappk ktype (mval e env kaddr) #:transparent)
(struct appk ktype (done todo env kaddr) #:transparent)
(struct appprimk ktype (op kaddr) #:transparent)
(struct primk ktype (op done todo env kaddr) #:transparent)
(struct letk ktype (vars done todo e env kaddr) #:transparent)

(define prims
  (hash '+ (prim +)
        '* (prim *)
        'equal? (prim equal?)
        'number? (prim number?)
        'boolean? (prim boolean?)
        'continuation? (prim ktype?)
        'list (prim list)
        'cons (prim cons)
        'car (prim car)
        'cdr (prim cdr)
        'null (prim (λ () null))))

(define (lambda-start? s)
  (match s
    [(or (== 'λ) (== 'lambda)) #t]
    [else #f]))
(define (lambda? e)
  (match e
    [`(,(? lambda-start?)
       (,_ ...) ,_) #t] ; standard multiarg lambda
    [`(,(? lambda-start?)
       ,(? symbol?) ,_) #t] ; varag lambda
    [else #f]))

; checks a syntactic expression to see
; if its an atomically evaluable expression
(define (atomic? v)
  (match v
    [(or (? symbol?) (? lambda?)
         (? number?) (? boolean?)
         `(quote ,_)) #t]
    [else #f]))

(define (atomic-eval st)
  (match-define (E sexpr p store _ _ _) st)
  (match sexpr
    [(? lambda?) (closure sexpr p)]
    [`(quote ,e) (quoteobj e)]
    [(or (? number?) (? boolean?)) sexpr]
    [(? symbol?) (hash-ref store (hash-ref p sexpr))]))

; just a helper function for updating a lot of keys at once
; to be used in a fold
(define update-hash (λ (k v res) (hash-set res k v)))

(define (alloc st offset)
  (match st
    [(E _ _ _ _ _ (time t)) (addr (+ t offset))]
    [(A _ _ _ _ (time t)) (addr (+ t offset))]))

(define (tick st amt)
  (match st
    [(E _ _ _ _ _ (time t)) (time (+ t amt))]
    [(A _ _ _ _ (time t)) (time (+ t amt))]))

(define (apply-step st)
  (match-define (A v store kstore kaddr t) st)
  (define k (hash-ref kstore kaddr))
  (match k
    [(mtk) st]
    [(ifk _ ef pk next-kaddr)
     #:when (equal? v #f)
     (E ef pk store kstore next-kaddr t)]
    [(ifk et _ pk next-kaddr)
     #:when (not (equal? v #f))
     (E et pk store kstore next-kaddr t)]
    [(letk vars not-done '() eb pk next-kaddr)
     (define as (map (λ (i) (alloc st i)) (range (length vars))))
     (define next-t (tick st (length vars)))
     (define done (append not-done (list v)))
     (define next-pk (foldl update-hash pk vars as))
     (define next-store (foldl update-hash store as done))
     (E eb next-pk next-store kstore next-kaddr next-t)]
    [(letk vars not-done (cons eh et) eb pk next-kaddr)
     (define next-next-kaddr (alloc st 0))
     (define next-t (tick st 1))
     (define next-k (letk vars (append not-done (list v)) et eb pk next-kaddr))
     (define next-kstore (hash-set kstore next-next-kaddr next-k))
     (E eh pk store next-kstore next-next-kaddr next-t)]
    [(setk a next-kaddr)
     (define next-store (hash-set store a v))
     (A (void) next-store kstore next-kaddr t)]
    [(callcck next-kaddr)
     #:when (closure? v)
     (match-define (closure `(,(? lambda-start?) (,x) ,e) plam) v)
     (define a (alloc st 0))
     (define next-t (tick st 1))
     ; reify next-kaddr and put into store
     (define next-k (hash-ref kstore next-kaddr))
     (define next-plam (hash-set plam x a))
     (define next-store (hash-set store a next-k))
     (E e next-plam next-store kstore next-kaddr t)]
    [(callcck _)
     #:when (ktype? v)
     (define next-k v)
     (define next-kaddr (alloc st 0))
     (define next-t (tick st 1))
     (define next-kstore (hash-set kstore next-kaddr next-k))
     (A k store next-kstore next-kaddr next-t)]
    [(appprimk (prim op) next-kaddr)
     (define next-v (apply op v))
     (A next-v store kstore next-kaddr t)]
    [(primk (prim op) not-done '() pk next-kaddr)
     (define next-v (apply op (append not-done (list v))))
     (A next-v store kstore next-kaddr t)]
    [(primk op done (cons eh et) pk next-kaddr)
     (define next-next-kaddr (alloc st 0))
     (define next-t (tick st 1))
     (define next-k (primk op (append done (list v)) et pk next-kaddr))
     (define next-kstore (hash-set kstore next-next-kaddr next-k))
     (E eh pk store next-kstore next-next-kaddr next-t)]
    [(appappk (closure `(,(? lambda-start?) (,xs ...) ,eb) plam) _ _ next-kaddr)
     (define as (map (λ (i) (alloc st i)) (range (length xs))))
     (define next-t (tick st (length xs)))
     (define next-plam (foldl update-hash plam xs as))
     (define next-store (foldl update-hash store as v))
     (E eb next-plam next-store kstore next-kaddr next-t)]
    [(appappk (closure `(,(? lambda-start?) ,(? symbol? x) ,eb) plam)
              _ _ next-kaddr)
     (define a (alloc st 0))
     (define next-t (tick st 1))
     (define next-plam (hash-set plam x a))
     (define next-store (hash-set store a v))
     (E eb next-plam next-store kstore next-kaddr next-t)]
    [(appappk '() e pk next-kaddr)
     (define next-next-kaddr (alloc st 0))
     (define next-t (tick st 1))
     (define next-k (appappk v e pk next-kaddr))
     (define next-kstore (hash-set kstore next-next-kaddr next-k))
     (E e pk store next-kstore next-next-kaddr next-t)]
    [(appk (cons (closure `(,(? lambda-start?) (,xs ...) ,eb) plam) notdone-vs)
           '() _ next-kaddr)
     (define as (map (λ (i) (alloc st i)) (range (length xs))))
     (define next-t (tick st (length xs)))
     (define vs (append notdone-vs (list v)))
     (define next-plam (foldl update-hash plam xs as))
     (define next-store (foldl update-hash store as vs))
     (E eb next-plam next-store kstore next-kaddr next-t)]
    [(appk (cons (closure `(,(? lambda-start?) ,(? symbol? x) ,eb) plam) notdone-vs)
           '() _ next-kaddr)
     (define a (alloc st 0))
     (define next-t (tick st 1))
     (define vs (append notdone-vs (list v)))
     (define next-plam (hash-set plam x a))
     (define next-store (hash-set store a vs))
     (E eb next-plam next-store kstore next-kaddr next-t)]
    [(appk (list (? ktype? klam)) '() pk next-kaddr)
     (define next-next-kaddr (alloc st 0))
     (define next-t (tick st 1))
     (define next-kstore (hash-set kstore next-next-kaddr klam))
     (A v store next-kstore next-next-kaddr next-t)]
    [(appk done (cons eh et) pk next-kaddr)
     (define next-next-kaddr (alloc st 0))
     (define next-t (tick st 1))
     (define next-k (appk (append done (list v)) et pk next-kaddr))
     (define next-kstore (hash-set kstore next-next-kaddr next-k))
     (E eh pk store next-kstore next-next-kaddr next-t)]))

(define (eval-step st)
  (match-define (E ctrl p store kstore kaddr t) st)
  (match ctrl
    [(? atomic?)
     (define v (atomic-eval st))
     (A v store kstore kaddr t)]
    [`(if ,ec ,et ,ef)
     (define next-kaddr (alloc st 0))
     (define next-t (tick st 1))
     (define k (ifk et ef p kaddr))
     (define next-kstore (hash-set kstore next-kaddr k))
     (E ec p store next-kstore next-kaddr next-t)]
    [`(let () ,e)
     (E e p store kstore kaddr t)]
    [`(let ([,x0 ,e0] [,xs ,es] ...) ,eb)
     (define next-kaddr (alloc st 0))
     (define next-t (tick st 1))
     (define k (letk (cons x0 xs) '() es eb p kaddr))
     (define next-kstore (hash-set kstore next-kaddr k))
     (E e0 p store next-kstore next-kaddr next-t)]
    [`(call/cc ,e)
     (define next-kaddr (alloc st 0))
     (define next-t (tick st 1))
     (define k (callcck kaddr))
     (define next-kstore (hash-set kstore next-kaddr k))
     (E e p store next-kstore next-kaddr next-t)]
    [`(set! ,(? symbol? x) ,e)
     (define next-kaddr (alloc st 0))
     (define next-t (tick st 1))
     (define a (hash-ref p x))
     (define k (setk a kaddr))
     (define next-kstore (hash-set kstore next-kaddr k))
     (E e p store next-kstore next-kaddr next-t)]
    [`(prim ,op)
     (match-define (prim pf) (hash-ref prims op))
     (define v (apply pf '()))
     (A v store kstore kaddr t)]
    [`(prim ,op ,e0 ,es ...)
     (define next-kaddr (alloc st 0))
     (define next-t (tick st 1))
     (define k (primk (hash-ref prims op) '() es p kaddr))
     (define next-kstore (hash-set kstore next-kaddr k))
     (E e0 p store next-kstore next-kaddr next-t)]
    [`(apply-prim ,op ,e)
     (define next-kaddr (alloc st 0))
     (define next-t (tick st 1))
     (define k (appprimk (hash-ref prims op) kaddr))
     (define next-kstore (hash-set kstore next-kaddr k))
     (E e p store next-kstore next-kaddr next-t)]
    [`(apply ,ef ,ex)
     (define next-kaddr (alloc st 0))
     (define next-t (tick st 1))
     (define k (appappk '() ex p kaddr))
     (define next-kstore (hash-set kstore next-kaddr k))
     (E ef p store next-kstore next-kaddr next-t)]
    [`(,ef ,es ...)
     (define next-kaddr (alloc st 0))
     (define next-t (tick st 1))
     (define k (appk '() es p kaddr))
     (define next-kstore (hash-set kstore next-kaddr k))
     (E ef p store next-kstore next-kaddr next-t)]))


; forms an initial state from an expression
(define (inject e) (E e (hash) (hash) (hash (addr 0) (mtk)) (addr 0) (time 1)))
(define fix? equal?)
; iterates an initial state until fixpoint
(define (evaluate program)
  (define state0 (inject program))
  (define (run st)
    (define nextst (match st
                     [(? E?) (eval-step st)]
                     [(? A?) (apply-step st)]))
    (if (fix? nextst st) st (run nextst)))
  (run state0))

(define e evaluate)
