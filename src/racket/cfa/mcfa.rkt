#lang racket

(require racket/hash)

(define m 1)

; this is a CESK* machine.
; it implements some basic scheme features like 'if', 'let',
; and multi argument functions. Also has numbers and booleans.

; eval and apply states
;
; eval will evaluate expressions
; apply will apply values to produce the next state.
(struct E (expr env store next-ak) #:transparent)
(struct A (val store next-ak) #:transparent)

; a binding address for 1CFA, which is the variable being bound, and the context (expr) its in.
(struct baddr (var ρ) #:transparent)
; a continuation address for kCFA, based on the P4F paper by Gilray et al.
(struct kaddr (ctx ρ) #:transparent)
(struct closure (lam env) #:transparent)
(struct prim (op) #:transparent)

(struct ktype () #:transparent) ; super-type for continuation frames
(struct mtk ktype () #:transparent)
(struct ifk ktype (et ef env ak) #:transparent)
(struct letk ktype (ctx vars done todo e env ak) #:transparent)
(struct callcck ktype (ctx ak) #:transparent)
(struct setk ktype (a ak) #:transparent)
(struct primk ktype (op done todo env ak) #:transparent)
(struct appprimk ktype (op ak) #:transparent)
(struct appk ktype (ctx done todo env ak) #:transparent)
(struct appappk ktype (ctx mval e env ak) #:transparent)

(struct aval (cval clos) #:transparent)

(define prims
  (hash '+ (prim (λ xs (foldl (λ (x res) ; this may erase clos cause im lazy
                                (match (cons x res)
                                  [(cons (aval 'TOP _) _) x]
                                  [(cons _ (aval 'TOP _)) res]
                                  [(cons (aval 'BOT _) _) (error "type error +")]
                                  [(cons _ (aval 'BOT _)) (error "type error +")]
                                  [(cons (aval x1 c1) (aval x2 c2))
                                   (aval (+ x1 x2) (set-union c1 c2))]))
                              (aval 0 (set)) xs)))
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
(define (atomic? ctrl)
  (match ctrl
    [(or (? symbol?) (? lambda?)
         (? number?) (? boolean?)
         `(quote ,_)) #t]
    [else #f]))

(define (join-avals oldv newv)
  (match-define (aval cv-new clos-new) newv)
  (match oldv
    [(aval 'BOT clos-old)
     (aval cv-new (set-union clos-old clos-new))]
    [(aval cv-old clos-old)
     #:when (equal? cv-new 'BOT)
     (aval cv-old (set-union clos-old clos-new))]
    [(aval cv-old clos-old)
     #:when (equal? cv-old cv-new)
     (aval cv-old (set-union clos-old clos-new))]
    [(aval _ clos-old)
     (aval 'TOP (set-union clos-old clos-new))]))

; take a single binding and add it to the store using the abstract semantics define
; in formalism.pdf
(define (store-join store k v)
  (match k
    [(kaddr _ _)
     (hash-update store k
                  (λ (oldv) (set-add oldv v))
                  (λ () (set v)))]
    [(baddr _ _)
     (hash-update store k
                  (λ (oldv) (join-avals oldv v))
                  (λ () v))]))

(define (newρ call ρ lam next-ρ)
  (match lam
    [(? lambda?) '()]
    [(? ktype?) '()]))
(define (allocb var ρ)
  (baddr var ρ))
(define (allock ctx ρ)
  (kaddr ctx ρ))

(define (atomic-eval st)
  (match-define (E sexpr p store _) st)
  (match sexpr
    [(? lambda?) (aval 'BOT (set (closure sexpr p)))]
    [`(quote ,(cons e _)) (aval e (set))] ; already quoted teehee ez metacircular
    [(or (? number?) (? boolean?)) (aval sexpr (set))]
    [(? symbol?) (hash-ref store (hash-ref p sexpr))]))

; takes an eval state, and returns the state that can be transitioned to.
; eval-stepping is deterministic, as its only evaluating syntax.
(define (eval-step st)
  (match-define (E eς ρ σ aκ) st)
  (match eς
    [(? atomic?)
     (define v (atomic-eval st))
     (A v σ aκ)]
    [`(if ,ec ,et ,ef)
     (define next-aκ (kalloc eς ρ))
     (define κ (ifk et ef ρ aκ))
     (define next-σ (store-join σ next-aκ κ))
     (E ec ρ next-σ next-aκ)]
    [`(let () ,eb) (E eb ρ σ aκ)]
    [`(let ([,x0 ,e0] [,xs ,es] ...) ,eb)
     (define next-aκ (kalloc eς ρ))
     (define κ (letk eς (cons x0 xs) '() es eb ρ aκ))
     (define next-σ (store-join σ next-aκ κ))
     (E e0 ρ next-σ next-aκ)]
    [`(call/cc ,e)
     (define next-aκ (kalloc eς ρ))
     (define κ (callcck eς ρ aκ))
     (define next-σ (store-join σ next-aκ κ))
     (E e ρ next-σ next-aκ)]
    [`(set! ,x ,e)
     (define next-aκ (kalloc eς ρ))
     (define a (hash-ref ρ x))
     (define κ (setk a aκ))
     (define next-σ (store-join σ next-aκ κ))
     (E e ρ next-σ next-aκ)]
    [`(prim ,ops)
     (match-define (prim op) (hash-ref prims ops))
     (A (op) σ aκ)]
    [`(prim ,op ,e0 ,es ...)
     (define next-aκ (kalloc eς ρ))
     (define κ (primk (hash-ref prims op) '() es ρ aκ))
     (define next-σ (store-join σ next-aκ κ))
     (E e0 ρ next-σ next-aκ)]
    [`(apply-prim ,op ,e)
     (define next-aκ (kalloc eς ρ))
     (define κ (appprimk (hash-ref prims op) aκ))
     (define next-σ (store-join σ next-aκ κ))
     (E e ρ next-σ next-aκ)]
    [`(apply ,ef ,ex)
     (define next-aκ (kalloc eς ρ))
     (define κ (appappk eς '() ex ρ aκ))
     (define next-σ (store-join σ next-aκ κ))
     (E ef ρ next-σ next-aκ)]
    [`(,ef ,es ...)
     (define next-aκ (kalloc eς ρ))
     (define κ (appk eς '() es ρ aκ))
     (define next-σ (store-join σ next-aκ κ))
     (E ef ρ next-σ next-aκ)]))

; takes an apply state, and returns a set of states that can be transitioned to.
; apply-stepping is non-deterministic, because values are abstract.
(define (apply-step st)
  (match-define (A v σ aκς) st)
  (define κς (hash-ref σ aκς))
  ; matches on the given continuation, returns a set of reachable states.
  (define (apply-step-single κ v σ aκς)
    (match κ
      [(mtk) (set)]
      [(ifk _ ef ρκ aκ)
       #:when (equal? v (aval #f (set)))
       (set (E ef ρκ σ aκ))]
      [(ifk et _ ρκ aκ)
       #:when (match v [(aval #f _) #f]
                     [(aval 'TOP _) #f]
                     [_ #t])
       (set (E et ρκ σ aκ))]
      [(ifk et ef ρκ aκ)
       (set (E et ρκ σ aκ)
            (E ef ρκ σ aκ))]
      [(letk eς vars done '() eb ρκ aκ)
       (define as (map (λ (x) (balloc x eς)) vars))
       (define next-ρκ (foldl (λ (k v res) (hash-set res k v)) ρκ vars as))
       (define next-done (append done (list v)))
       (define next-σ (foldl (λ (k v res) (store-join σ k v)) σ as next-done))
       (set (E eb next-ρκ next-σ aκ))]
      [(letk eς vars done (cons eh et) eb ρκ aκ)
       (define next-aκ (kalloc eς ρκ))
       (define κ (letk eς vars (append done (list v)) et eb ρκ aκ))
       (define next-σ (store-join σ next-aκ κ))
       (set (E eh ρκ next-σ next-aκ))]
      [(setk a aκ)
       (define next-σ (store-join σ a v))
       (set (A (aval (void) (set)) next-σ aκ))]
      [(callcck eς aκ)
       (match-define (aval cv clos) v)
       (set-union
        (if (ktype? cv)
            (let ([next-σ (store-join σ aκς cv)])
                  (set (A κς next-σ aκς)))
            (set))
        (foldl
         set-union (set)
         (set-map
          clos
          (λ (clo)
            (match clo
              [(closure `(,_ (,x) ,eb) ρλ)
               (define a (balloc x eς))
               (define κs (hash-ref σ aκ))
               (define next-ρλ (hash-set ρλ x a))
               (list->set
                (set-map κs
                         (λ (κ)
                           (define next-σ (store-join σ a κ))
                           (set (E eb next-ρλ next-σ aκ)))))])))))]
      [(appprimk (prim op) aκ)
       (define next-v (apply op v))
       (set (A next-v σ aκ))]
      [(primk (prim op) done '() _ aκ)
       (define next-v (apply op (append done (list v))))
       (set (A next-v σ aκ))]
      [(primk op done (cons eh et) ρκ aκ)
       (define next-aκ (kalloc eh ρκ))
       (define κ (primk op (append done (list v)) et ρκ aκ))
       (define next-σ (store-join σ next-aκ κ))
       (set (E eh ρκ next-σ next-aκ))]
      [(appappk eς vf ex ρκ aκ)
       (match-define (aval cv clos) vf)
       (set-union
        (if (or (equal? cv 'TOP) (equal? cv '()))
            (let* ([next-aκ (kalloc ex ρκ)]
                   [κ (appappk eς v ex ρκ aκ)]
                   [next-σ (store-join σ next-aκ κ)])
              (set (E ex ρκ next-σ next-aκ)))
            (set))
        (list->set
         (set-map
          clos
          (λ (clo)
            (match clo
              [(closure `(,_ (,xs ...) ,eb) ρλ)
               (define as (map (λ (x) (balloc x eς)) xs))
               (define next-ρλ (foldl (λ (k v res) (hash-set res k v)) ρλ xs as))
               (define next-σ (foldl (λ (k v res) (store-join res k v)) σ as v))
               (E eb next-ρλ next-σ aκ)]
              [(closure `(,_ ,x ,eb) ρλ)
               (define a (balloc x eς))
               (define next-ρλ (hash-set ρλ x a))
               (define next-σ (store-join σ a v))
               (E eb next-ρλ next-σ)])))))]
      [(appk eς done (cons eh et) ρκ aκ)
       (define next-aκ (kalloc eh ρκ))
       (define κ (appk eς (append done (list v)) et ρκ aκ))
       (define next-σ (store-join σ next-aκ κ))
       (set (E eh ρκ next-σ next-aκ))]
      [(appk eς (cons vh vt) '() ρκ aκ)
       (match-define (aval cv clos) vh)
       (set-union
        (if (or (ktype? cv) (equal? cv 'TOP))
            (let* ([aκ (kalloc eς ρκ)]
                   [next-σ (store-join σ aκ cv)])
              (set (A v next-σ aκ)))
            (set))
        (list->set
         (set-map
          clos
          (λ (clo)
            (match clo
              [(closure `(,_ (,xs ...) ,eb) ρλ)
               (define as (map (λ (x) (balloc x eς)) xs))
               (define next-ρλ (foldl (λ (k v res) (hash-set res k v)) ρλ xs as))
               (define next-vt (append vt (list v)))
               (define next-σ (foldl (λ (k v res) (store-join res k v)) σ as next-vt))
               (E eb next-ρλ next-σ aκ)]
              [(closure `(,_ ,x ,eb) ρλ)
               (define a (balloc x eς))
               (define next-ρλ (hash-set ρλ x a))
               (define next-vt (append vt (list v)))
               (define next-σ (store-join σ a next-vt))
               (E eb next-ρλ next-σ aκ)])))))]))
  ; each element of the resulting list is a set of reachable states, so just union them together.
  (foldl set-union (set) (set-map κς (λ (κ) (apply-step-single κ v σ aκς)))))

; forms an initial state from an expression
(define (inject e)
  (define kaddr0 (kalloc "" (hash)))
  (E e (hash) (hash kaddr0 (set (mtk))) kaddr0))

(define fix? equal?)

; iterates an initial state until there is no more new states
(define (store-combine σ1 σ2)
  (hash-union σ1 σ2
              #:combine/key (λ (_ a b) (join-avals a b))))

(define (eval program)
  (define (step ς)
    (match ς
      [(? E?) (set (eval-step ς))]
      [(? A?) (apply-step ς)]))
  (define (combine ςs)
    (define global
      (foldl (λ (ς res) (match ς
                          [(E _ _ σ _)
                           (store-combine res σ)]
                          [(A _ σ _)
                           (store-combine res σ)]))
             (hash) (set->list ςs)))
    (list->set
     (set-map
      ςs (λ (ς) (match ς
                  [(E c e s k) (E c e global k)]
                  [(A c s k) (A c global k)])))))
  (define (run cfg todo)
    (match todo
      ['() cfg]
      [(cons doing tail)
       (if (hash-has-key? cfg doing)
           (run cfg tail)
           (let* ([stepped (step doing)]
                  [combined (combine stepped)]
                  [cfg (hash-set cfg doing combined)]
                  [todo (append (set->list combined) todo)])
             (run cfg todo)))]))
  (run (hash) (list (inject program))))

(define e eval)
