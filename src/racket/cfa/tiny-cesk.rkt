#lang racket

; this is a time-stamped CESK* machine, with a globalized store.
; it implements some basic scheme features like 'if', 'let',
; and multi argument functions. Also has numbers and booleans.

; eval and apply states
;
; eval will evaluate expressions
; apply will apply values to produce the next state.
(struct E (sexpr env store next-ak) #:transparent)
(struct A (val store next-ak) #:transparent)

(struct baddr (addr offset) #:transparent)
(struct kaddr (addr) #:transparent)

(struct closure (lam env) #:transparent)
(struct prim (op) #:transparent)

(struct ktype () #:transparent) ; super-type for continuation frames
(struct mtk ktype () #:transparent)
(struct ifk ktype (et ef env ak) #:transparent)
(struct letk ktype (vars done todo e env ak) #:transparent)
(struct callcck ktype (ak) #:transparent)
(struct setk ktype (a ak) #:transparent)
(struct primk ktype (op done todo env ak) #:transparent)
(struct appprimk ktype (op ak) #:transparent)
(struct appk ktype (done todo env ak) #:transparent)
(struct appappk ktype (mval e env ak) #:transparent)

(define prims
  (hash '+ (prim +)
        '* (prim *)
        'equal? (prim equal?) 'number? (prim number?) 'boolean? (prim boolean?)
        'continuation? (prim ktype?)
        'null? (prim null?) 'cons? (prim cons?) 'list? (prim list?)
        'list (prim list) 'cons (prim cons) 'car (prim car) 'cdr (prim cdr)
        'null (prim (λ () null)))) ; make null a function because... i dont wanna add to starting env.

; checks if a symbol is lambda or λ
(define (λ-start? s)
  (match s
    [(or (== 'λ) (== 'lambda)) #t]
    [else #f]))

(define (lambda? e)
  (match e
    [`(,(? λ-start?)
       (,_ ...) ,_) #t] ; standard multiarg lambda
    [`(,(? λ-start?)
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

; takes a list of cons bindings and adds them to the given store
; in the concrete, this is equivalent to a simple hash-set
(define (store-join store bnds)
  (foldl (λ (kv res) (hash-set res (car kv) (cdr kv))) store bnds))

; the address will do for now
; (and make the output a lot smaller!)
; the semantics require a K but its okay to cheat a bit,
; in the conrete there will be no difference.
(define (balloc st n)
  (match st
    [(E _ _ store _) (baddr (hash-count store) n)]
    [(A _ store _) (baddr (hash-count store) n)]))

(define (kalloc st)
  (match st
    [(E _ _ store _) (kaddr (hash-count store))]
    [(A _ store _) (kaddr (hash-count store))]))

(define (atomic-eval st)
  (match-define (E sexpr p store _) st)
  (match sexpr
    [(? lambda?) (closure sexpr p)]
    [`(quote ,e) e] ; already quoted teehee ez metacircular
    [(or (? number?) (? boolean?)) sexpr]
    [(? symbol?) (hash-ref store (hash-ref p sexpr))]))

; steps an eval state to the next state.
(define (eval-step st)
  (match-define (E expr env store ak) st)
  (match expr
    [(? atomic?)
     (define v (atomic-eval st))
     (A v store ak)]
    [`(if ,ec ,et ,ef)
     (define next-ak (kalloc st))
     (define k (ifk et ef env ak))
     (define next-store (store-join store (list (cons next-ak k))))
     (E ec env next-store next-ak)]
    [`(let () ,eb) (E eb env store ak)]
    [`(let ([,x0 ,e0] [,xs ,es] ...) ,eb)
     (define next-ak (kalloc st))
     (define k (letk (cons x0 xs) '() es eb env ak))
     (define next-store (store-join store (cons next-ak k)))
     (E e0 env next-store next-ak)]
    [`(call/cc ,e)
     (define next-ak (kalloc st))
     (define k (callcck ak))
     (define next-store (store-join store (list (cons ak k))))
     (E e env next-store next-ak)]
    [`(set! ,x ,e)
     (define next-ak (kalloc st))
     (define ab (hash-ref env x))
     (define k (setk ab ak))
     (define next-store (store-join store (list (cons next-ak k))))
     (E e env next-store next-ak)]
    [`(prim ,ops)
     (match-define (prim op) (hash-ref prims ops))
     (define v (op))
     (A v store ak)]
    [`(prim ,op ,e0 ,es ...)
     (define next-ak (kalloc st))
     (define k (primk (hash-ref prims op) '() es env ak))
     (define next-store (store-join store (list (cons next-ak k))))
     (E e0 env next-store next-ak)]
    [`(apply-prim ,op ,e)
     (define next-ak (kalloc st))
     (define k (appprimk (hash-ref prims op) ak))
     (define next-store (store-join store (list (cons next-ak k))))
     (E e env next-store next-ak)]
    [`(apply ,ef ,ex)
     (define next-ak (kalloc st))
     (define k (appappk '() ex env ak))
     (define next-store (store-join store (list (cons next-ak k))))
     (E ef env next-store next-ak)]
    [`(,ef ,es ...)
     (define next-ak (kalloc st))
     (define k (appk '() es env ak))
     (define next-store (store-join store (list (cons next-ak k))))
     (E ef env next-store next-ak)]))

; steps an apply state to the next state
(define (apply-step st)
  (match-define (A v store ak) st)
  (define k (hash-ref store ak))
  (match k
    [(mtk) st]
    [(ifk _ ef kenv next-ak)
     #:when (equal? v #f)
     (E ef kenv store next-ak)]
    [(ifk et _ kenv next-ak)
     (E et kenv store next-ak)]
    [(letk vars done '() ebody kenv next-ak)
     (define as (map (λ (i) (balloc st i)) (range vars)))
     (define next-done (append done (list v)))
     (define next-kenv (foldl (λ (k v res) (hash-set res k v)) kenv vars as))
     (define next-store (store-join store (map cons as next-done)))
     (E ebody next-kenv next-store next-ak)]
    [(letk vars done (cons eh et) eb kenv next-ak)
     (define next-next-ak (kalloc st))
     (define next-k (letk vars (append done (list v)) et eb kenv next-ak))
     (define next-store (store-join store (list (cons next-next-ak next-k))))
     (E eh kenv next-store next-next-ak)]
    [(setk a next-ak)
     (define next-store (store-join store (list (cons a v))))
     (A (void) next-store next-ak)]
    [(callcck next-ak)
     #:when (closure? v)
     (match-define (closure `(,_ (,x) ,e) lamenv) v)
     (define a (balloc st 0))
     (define next-k (hash-ref store next-ak))
     (define next-lamenv (hash-set lamenv x a))
     (define next-store (store-join store (list (cons a next-k))))
     (E e next-lamenv next-store next-ak)]
    [(callcck _)
     #:when (ktype? v)
     (define next-ak (kalloc st))
     (define next-store (store-join store (list (cons next-ak v))))
     (A k next-store next-ak)]
    [(appprimk (prim op) next-ak)
     (define next-v (apply op v))
     (A next-v store next-ak)]
    [(primk (prim op) done '() _ next-ak)
     (define next-v (apply op (append done (list v))))
     (A next-v store next-ak)]
    [(primk op done (cons eh et) kenv next-ak)
     (define next-next-ak (kalloc st))
     (define next-k (primk op (append done (list v)) et kenv next-ak))
     (define next-store (store-join store (list (cons next-next-ak next-k))))
     (E eh kenv next-store next-next-ak)]
    [(appappk (closure `(,(? λ-start?) (,xs ...) ,eb) lamenv) _ _ next-ak)
     (define as (map (λ (i) (balloc st i)) (range (length xs))))
     (define next-lamenv (foldl (λ (k v res) (hash-set res k v)) lamenv xs as))
     (define next-store (store-join store (map cons as v)))
     (E eb next-lamenv next-store next-ak)]
    [(appappk (closure `(,(? λ-start?) ,x ,eb) lamenv) _ _ next-ak)
     (define a (balloc st 0))
     (define next-lamenv (hash-set lamenv x a))
     (define next-store (store-join store (list (cons a v))))
     (E eb next-lamenv next-store next-ak)]
    [(appappk '() e kenv next-ak)
     (define next-next-ak (kalloc st))
     (define next-k (appappk v e kenv next-ak))
     (define next-store (store-join store (list (cons next-next-ak next-k))))
     (E e kenv next-store next-next-ak)]
    [(appk (cons (closure `(,(? λ-start?) (,xs ...) ,eb) lamenv) vs) '() _ next-ak)
     (define as (map (λ (i) (balloc st i)) (range (length xs))))
     (define next-vs (append vs (list v)))
     (define next-lamenv (foldl (λ (k v res) (hash-set res k v)) lamenv xs as))
     (define next-store (store-join store (map cons as next-vs)))
     (E eb next-lamenv next-store next-ak)]
    [(appk (cons (closure `(,(? λ-start?) ,x ,eb) lamenv) vs) '() _ next-ak)
     (define a (balloc st 0))
     (define next-vs (append vs (list v)))
     (define next-lamenv (hash-set lamenv x a))
     (define next-store (store-join store (list (cons a next-vs))))
     (E eb next-lamenv next-store next-ak)]
    [(appk (list (? ktype? lamk)) '() kenv next-ak)
     (define next-next-ak (kalloc st))
     (define next-store (store-join store (list (cons next-next-ak lamk))))
     (A v next-store next-next-ak)]
    [(appk done (cons eh et) kenv next-ak)
     (define next-next-ak (kalloc st))
     (define next-k (appk (append done (list v)) et kenv next-ak))
     (define next-store (store-join store (list (cons next-next-ak next-k))))
     (E eh kenv next-store next-next-ak)]))


; forms an initial state from an expression
(define (inject e) (E e (hash) (hash (kaddr 0) (mtk)) (kaddr 0)))
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
