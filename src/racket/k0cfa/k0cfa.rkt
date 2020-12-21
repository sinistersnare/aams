#lang racket

; this is a time-stamped CESK* machine, with a globalized store.
; it implements some basic scheme features like 'if', 'let',
; and multi argument functions. Also has numbers and booleans.

; eval and apply states
;
; eval will evaluate expressions
; apply will apply values to produce the next state.
(struct E (sexpr env store kstore nextkaddr) #:transparent)
(struct A (val store kstore nextkaddr) #:transparent)

(struct addr (kont label offset) #:transparent)
(struct closure (lam env) #:transparent)
(struct prim (op) #:transparent)

(struct ktype () #:transparent) ; super-type for continuation frames
(struct mtk ktype () #:transparent)
(struct ifk ktype (et ef env kaddr) #:transparent)
(struct callcck ktype (kaddr label) #:transparent)
(struct setk ktype (a kaddr) #:transparent)
(struct appappk ktype (mval e env kaddr label) #:transparent)
(struct appk ktype (done todo env kaddr label) #:transparent)
(struct appprimk ktype (op kaddr) #:transparent)
(struct primk ktype (op done todo env kaddr label) #:transparent)
(struct letk ktype (vars done todo e env kaddr label) #:transparent)

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

; takes a list of cons bindings and adds them to the given store
; in the concrete, this is equivalent to a simple hash-set
(define (store-set store bnds)
  (foldl (λ (kv res) (hash-set res (car kv) (cdr kv))) store bnds))

(define (alloc st l offset)
  (define k (match st
              [(E _ _ _ kstore kaddr) (hash-ref kstore kaddr)]
              [(A _ _ kstore kaddr) (hash-ref kstore kaddr)]))
  (addr k l offset))

(define (atomic-eval st)
  (match-define (E (cons sexpr l) p store _ _) st)
  (match sexpr
    [(? lambda?) (closure sexpr p)]
    [`(quote ,(cons e _)) e] ; already quoted teehee ez metacircular
    [(or (? number?) (? boolean?)) sexpr]
    [(? symbol?) (hash-ref store (hash-ref p sexpr))]))

(define (eval-step st)
  #;(displayln `(EVAL: ,st))
  (match-define (E (cons expr label) p store kstore kaddr) st)
  (match expr
    [(? atomic?)
     (define v (atomic-eval st))
     (A v store kstore kaddr)]
    [`(if ,ec ,et ,ef)
     (define next-kaddr (alloc st label 0))
     (define k (ifk et ef p kaddr))
     (define next-kstore (store-set kstore (list (cons next-kaddr k))))
     (E ec p store next-kstore next-kaddr)]
    [`(let () ,e) (E e p store kstore kaddr)]
    [`(let ([,x0 ,e0] [,xs ,es] ...) ,eb)
     (define next-kaddr (alloc st label 0))
     (define k (letk (cons x0 xs) '() es eb p kaddr label))
     (define next-kstore (store-set kstore (list (cons next-kaddr k))))
     (E e0 p store next-kstore next-kaddr)]
    [`(call/cc ,e)
     (define next-kaddr (alloc st label 0))
     (define k (callcck kaddr label))
     (define next-kstore (store-set kstore
                                    (list (cons next-kaddr k))))
     (E e p store next-kstore next-kaddr)]
    [`(set! ,x ,e)
     (define next-kaddr (alloc st label 0))
     (define addr (hash-ref p x))
     (define k (setk addr kaddr))
     (define next-kstore (store-set kstore
                                    (list (cons next-kaddr k))))
     (E e p store next-kstore next-kaddr)]
    [`(prim ,op)
     (match-define (prim pf) (hash-ref prims op))
     (define v (apply pf '()))
     (A v store kstore kaddr)]
    [`(prim ,op ,e0 ,es ...)
     (define next-kaddr (alloc st label 0))
     (define k (primk (hash-ref prims op) '() es p kaddr label))
     (define next-kstore (store-set kstore
                                    (list (cons next-kaddr k))))
     (E e0 p store next-kstore next-kaddr)]
    [`(apply-prim ,op ,e)
     (define next-kaddr (alloc st label 0))
     (define k (appprimk (hash-ref prims op) kaddr))
     (define next-kstore (store-set kstore
                                    (list (cons next-kaddr k))))
     (E e p store next-kstore next-kaddr)]
    [`(apply ,ef ,ex)
     (define next-kaddr (alloc st label 0))
     (define k (appappk '() ex p kaddr label))
     (define next-kstore (store-set kstore
                                    (list (cons next-kaddr k))))
     (E ef p store kstore next-kaddr)]
    [`(,ef ,es ...)
     (define next-kaddr (alloc st label 0))
     (define k (appk '() es p kaddr label))
     (define next-kstore (store-set kstore
                                    (list (cons next-kaddr k))))
     (E ef p store next-kstore next-kaddr)]))

(define (apply-step st)
  #;(displayln `(APPLY: ,st))
  (match-define (A v store kstore kaddr) st)
  (define k (hash-ref kstore kaddr))
  (match k
    [(mtk) st]
    [(ifk et ef pk next-kaddr)
     #:when (false? v)
     (E ef pk store kstore next-kaddr)]
    [(ifk et ef pk next-kaddr)
     #:when (not (false? v))
     (E et pk store kstore next-kaddr)]
    [(letk vars done '() eb pk next-kaddr label)
     (define as (map (λ (i) (alloc st label i)) (range (length vars))))
     (define next-done (append done (list v)))
     (define next-pk (foldl (λ (k v res) (hash-set res k v)) pk vars as))
     (define next-store (store-set store
                                   (map (λ (a v) (cons a v)) as next-done)))
     (E eb next-pk next-store kstore next-kaddr)]
    [(letk vars done (cons eh et) eb pk next-kaddr label)
     (define next-next-kaddr (alloc st label 0))
     (define next-k (letk vars (append done (list v)) et eb pk next-kaddr))
     (define next-kstore (store-set kstore (list (cons next-next-kaddr next-k))))
     (E eh pk store next-kstore next-next-kaddr)]
    [(setk addr next-kaddr)
     (define next-store (store-set store (list (cons addr v))))
     (A (void) next-store kstore next-kaddr)]
    [(callcck next-kaddr label)
     #:when (closure? v)
     (match-define (closure `(,(? lambda-start?) (,(? symbol? x)) ,e) plam) v)
     (define addr (alloc st label 0))
     (define next-k (hash-ref kstore next-kaddr))
     (define next-plam (hash-set plam x addr))
     (define next-store (store-set store (list (cons addr next-k))))
     (E e next-plam next-store kstore next-kaddr)]
    [(callcck _ label)
     #:when (ktype? v)
     (define next-k v)
     (define next-kaddr (alloc st label 0))
     (define next-kstore (store-set kstore (list (cons next-kaddr next-k))))
     (A k store next-kstore next-kaddr)]
    [(appprimk (prim op) next-kaddr)
     (define next-v (apply op v))
     (A next-v store kstore next-kaddr)]
    [(primk (prim op) done '() _ next-kaddr _)
     (define next-v (apply op (append done (list v))))
     (A next-v store kstore next-kaddr)]
    [(primk op done (cons eh et) pk next-kaddr label)
     (define next-next-kaddr (alloc st label 0))
     (define next-k (primk op (append done (list v)) et pk next-kaddr label))
     (define next-kstore (store-set kstore (list (cons next-next-kaddr next-k))))
     (E eh pk store next-kstore next-next-kaddr)]
    [(appappk (closure `(,(? lambda-start?) (,xs ...) ,eb) plam) _ _ next-kaddr label)
     (define as (map (λ (i) (alloc st label i)) (range (length xs))))
     (define next-plam (foldl (λ (k v res) (hash-set res k v)) plam xs as))
     (define next-store (store-set store (map (λ (a v) (cons a v))) as v))
     (E eb next-plam next-store kstore next-kaddr)]
    [(appappk (closure `(,(? lambda-start?) ,(? symbol? x) ,eb) plam) _ _ next-kaddr label)
     (define addr (alloc st label 0))
     (define next-plam (hash-set plam x addr))
     (define next-store (store-set store (list (cons addr v))))
     (E eb next-plam next-store kstore next-kaddr)]
    [(appappk '() e pk next-kaddr label)
     (define next-next-kaddr (alloc st label 0))
     (define next-k (appappk v e pk next-kaddr label))
     (define next-kstore (store-set kstore (list (cons next-next-kaddr next-k))))
     (E e pk store next-kstore next-next-kaddr)]
    [(appk (cons (closure `(,(? lambda-start?) (,xs ...) ,eb) plam) vs) '() _ next-kaddr label)
     (define as (map (λ (i) (alloc st label i)) (range (length xs))))
     (define next-vs (append vs (list v)))
     (define next-plam (foldl (λ (k v res) (hash-set res k v)) plam xs as))
     (define next-store (store-set store
                                   (map (λ (a v) (cons a v)) as next-vs)))
     (E eb next-plam next-store kstore next-kaddr)]
    [(appk (cons (closure `(,(? lambda-start?) ,(? symbol? x) ,eb) plam) vs) '() _ next-kaddr label)
     (define addr (alloc st label 0))
     (define next-vs (append vs (list v)))
     (define next-plam (hash-set plam x addr))
     (define next-store (store-set store (list (cons addr next-vs))))
     (E eb next-plam next-store kstore next-kaddr)]
    [(appk (list (? ktype? klam)) '() pk next-kaddr label)
     (define next-next-kaddr (alloc st label 0))
     (define next-kstore (store-set (list (cons next-next-kaddr klam))))
     (A v store next-kstore next-next-kaddr)]
    [(appk done (cons eh et) pk next-kaddr label)
     (define next-next-kaddr (alloc st label 0))
     (define next-k (appk (append done (list v)) et pk next-kaddr label))
     (define next-kstore (store-set kstore (list (cons next-next-kaddr next-k))))
     (E eh pk store next-kstore next-next-kaddr)]))


; labels an expression so it can be uniquely identified from another
; expression that is syntactically equivalent in another place.
; e -> cons(e, lab)
; do that recursively thru e.
(define (label expr)
  (define f (λ (ne) (cons ne (gensym 'label))))
  ; use an inner function so we can close over `f`
  (define (do expr)
    (f
     (match expr
       [`(,(? lambda-start? lam) ,bnds ,body) `(,lam ,bnds ,(do body))]
       [`(quote ,e) `(quote ,(do e))]
       [(? atomic?) expr]
       [`(if ,ec ,et ,ef) `(if ,(do ec) ,(do et) ,(do ef))]
       [`(let ([,xs ,es] ...) ,ebody) `(let ,(map (λ (x ex) `(,x ,(do ex))) xs es) ,(do ebody))]
       [`(call/cc ,e) `(call/cc ,(do e))]
       [`(set! ,x ,e) `(set! ,x ,(do e))]
       [`(prim ,op ,es ...) `(prim ,op ,@(map do es))]
       [`(apply-prim ,op ,e) `(apply-prim ,op ,(do e))]
       [`(apply ,ef ,ex) `(apply ,(do ef) ,(do ex))]
       [`(,es ...) (map do es)])))
  (do expr))

; forms an initial state from an expression
(define (inject e) (E e (hash) (hash) (hash (addr (mtk) '0 0) (mtk)) (addr (mtk) '0 0)))
(define fix? equal?)
; iterates an initial state until fixpoint
(define (evaluate program)
  (define state0 (inject (label program)))
  (define (run st)
    (define nextst (match st
                     [(? E?) (eval-step st)]
                     [(? A?) (apply-step st)]))
    (if (fix? nextst st) st (run nextst)))
  (run state0))

(define e evaluate)

