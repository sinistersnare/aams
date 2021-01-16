#lang racket

; this file is a CESK implementation of Scheme
; based on the formalization found in this repo.
;
; The interesting thing about this machine is its use of
; flat-allocated closures. Meaning, instead of linking environments
; together, variables are copied into the closures unique environment.

; state types
(struct E (e ρ σ aκ) #:transparent)
(struct A (v ρ σ aκ) #:transparent)

; address types
(struct baddr (x ρ) #:transparent)
(struct kaddr (n) #:transparent)

; a closure is just a syntactic lambda
; and an environment to find its free variables
; in this machine, the env is unique to the closure
; and is not shared elsewhere.
(struct closure (lam ρ) #:transparent)

; an environment in this machine is a unique number (so no clashes)
; and the call stack for this environment.
;
; in the abstract the number is dropped, and approximation is achieved.
(struct env (n call-list) #:transparent)

; Continuation types
; parent type of continuation, so we can do (ktype? k)
(struct ktype () #:transparent)
(struct mtk ktype () #:transparent)
(struct ifk ktype (et ef ρ aκ) #:transparent)
(struct setk ktype (a aκ) #:transparent)
(struct callcck ktype (callccexp aκ) #:transparent)
(struct applyk ktype (applyexp maybe-v e ρ aκ) #:transparent)
(struct callk ktype (call done todo ρ aκ) #:transparent)

; option some so we can differentiate between None and Some in
; maybe-v in the applyk continuation frame.
; otherwise (apply '() _) would be an infinite loop.
(struct someval (v) #:transparent)

; primitive functions, implemented by the implementation
(struct prim (op))
(define prims
  (hash '+ (prim +)
        '- (prim -)
        'cons (prim cons)
        'car (prim car)
        'cdr (prim cdr)
        'length (prim length)))

; checks if a symbol is lambda or λ
(define (λ-start? s)
  (match s
    [(or (== 'λ) (== 'lambda)) #t]
    [else #f]))

; checks if the expression given is a lambda expression
(define (λ? e)
  (match e
    ; standard multiarg lambda
    [`(,(? λ-start?) (,_ ...) ,_) #t]
    ; vararg lambda
    [`(,(? λ-start?) ,(? symbol?) ,_) #t]
    [else #f]))

; checks a syntactic expression to see
; if its an atomically evaluable expression
(define (atomic? v)
  (match v
    [(or (? symbol?) (? λ?)
         (? number?) (? boolean?)
         `(quote ,_)) #t]
    [_ #f]))

; STORE
;
; join in the concrete semantics is defined as
; a simple extension of the set.
(define σ-join hash-set)
(define σ-ref hash-ref)
(define σ-has-key? hash-has-key?)
(define σ-count hash-count)

; ENVIRONMENT
;
; To make a new environment, you simply append
; the newest call to the stack, and increment the address
(define (ρ-new call ρ)
  (match-define (env n call-list) ρ)
  (env (add1 n) (cons call call-list)))

; finds all variables that do not have a binding
; inside of the expression.
;
; returns a list of all unbound vars.
(define (find-free-vars e bound)
  (match e
    [`(,(? λ-start?) (,xs ...) ,eb)
     (find-free-vars eb (foldl (λ (x s) (set-add s x)) bound xs))]
    [`(,(? λ-start?) ,x ,eb)
     (find-free-vars eb (set-add bound x))]
    [(? symbol?) ; check if its bound or its a prim
     (if (or (set-member? bound e) (hash-has-key? prims e))
         '() (list e))]
    [(or (? number?) (? boolean?) `(quote ,_)) '()]
    [`(if ,ec ,et ,ef)
     (append (find-free-vars ec bound)
             (find-free-vars et bound)
             (find-free-vars ef bound))]
    [`(set! ,x ,e)
     (append (if (set-member? bound x) '() (list x))
             (find-free-vars e bound))]
    [`(call/cc ,e) (find-free-vars e bound)]
    [`(apply ,ef ,ea)
     (append (find-free-vars ef bound) (find-free-vars ea bound))]
    [`(let ([,xs ,es] ...) ,eb)
     (append (foldl (λ (e r) (append (find-free-vars e bound) r)) '() es)
             (find-free-vars eb (foldl (λ (x r) (set-add r x)) bound xs)))]
    [`(,es ...)
     (foldl (λ (e t) (append t (find-free-vars e bound))) '() es)]
    [_ (error (format "We do not cover the case of '~a'" e))]))

(define (atomic-eval ς)
  (match-define (E e ρ σ _) ς)
  (match e
    [(or (? boolean?) (? number?)) e]
    [`(quote ,e) e] ; already quoted :)
    [(? symbol?)
     #:when (and (not (σ-has-key? σ (baddr e ρ)))
                 (hash-has-key? prims e))
     (hash-ref prims e)]
    [(? λ?) (closure e ρ)]
    [(? symbol?) (σ-ref σ (baddr e ρ))]))

(define (callfunc head args ρ σ ctx aκ)
  (match head
    [(closure `(,_ (,xs ...) ,eb) ρλ)
     (define next-ρ (ρ-new ctx ρ))
     (define arg-addrs (map (λ (x) (baddr x next-ρ)) xs))
     (define free-vars (find-free-vars `(λ ,xs ,eb) (set)))
     (define free-addrs (map (λ (x) (baddr x next-ρ)) free-vars))
     (define free-vals (map (λ (x) (σ-ref σ (baddr x ρλ))) free-vars))
     (define next-σ
       (foldl (λ (k v res) (σ-join res k v))
              σ (append free-addrs arg-addrs)
              (append free-vals args)))
     (E eb next-ρ next-σ aκ)]
    [(closure `(,_ ,x ,eb) ρλ)
     (define next-ρ (ρ-new ctx ρ))
     (define arg-addr (baddr x next-ρ))
     (define free-vars (find-free-vars `(λ ,x ,eb) (set)))
     (displayln `(freevrs: ,free-vars))
     (define free-addrs (map (λ (x) (baddr x next-ρ)) free-vars))
     (define free-vals (map (λ (x) (σ-ref σ (baddr x ρλ))) free-vars))
     (define next-σ
       (foldl (λ (k v res) (σ-join res k v))
              (σ-join σ arg-addr args)
              free-addrs free-vals))
     (E eb next-ρ next-σ aκ)]
    [(? ktype? κ)
     (match-define (list v) args)
     (define next-aκ (kaddr (σ-count σ)))
     (define next-σ (σ-join σ next-aκ κ))
     (A v ρ next-σ next-aκ)]
    [(prim op)
     (define v (apply op args))
     (A v ρ σ aκ)]))

(define (step-eval ς)
  (match-define (E eς ρ σ aκ) ς)
  (match eς
    [(? atomic?)
     (define v (atomic-eval ς))
     (A v ρ σ aκ)]
    [`(if ,ec ,et ,ef)
     (define next-aκ (kaddr (σ-count σ)))
     (define κ (ifk et ef ρ aκ))
     (define next-σ (σ-join σ next-aκ κ))
     (E ec ρ next-σ next-aκ)]
    [`(let ([,xs ,es] ...) ,eb)
     (E `((λ ,xs ,eb) ,@es) ρ σ aκ)]
    [`(set! ,x ,e)
     (define a (baddr x ρ))
     (define next-aκ (kaddr (σ-count σ)))
     (define κ (setk a aκ))
     (define next-σ (σ-join σ next-aκ κ))
     (E e ρ next-σ next-aκ)]
    [`(call/cc ,e)
     (define next-aκ (kaddr (σ-count σ)))
     (define κ (callcck eς aκ))
     (define next-σ (σ-join σ next-aκ κ))
     (E e ρ next-σ next-aκ)]
    [`(apply ,ef,e)
     (define next-aκ (kaddr (σ-count σ)))
     (define κ (applyk eς '() e ρ aκ))
     (define next-σ (σ-join σ next-aκ κ))
     (E ef ρ next-σ next-aκ)]
    [`(,ef ,es ...)
     (define next-aκ (kaddr (σ-count σ)))
     (define κ (callk eς '() es ρ aκ))
     (define next-σ (σ-join σ next-aκ κ))
     (E ef ρ next-σ next-aκ)]))

(define (step-apply ς)
  (match-define (A v ρ σ aκ) ς)
  (define κς (σ-ref σ aκ))
  (match κς
    [(mtk) ς]
    [(ifk et _ ρκ next-aκ)
     #:when (not (equal? v #f))
     (E et ρκ σ next-aκ)]
    [(ifk _ ef ρκ next-aκ)
     #:when (equal? v #f)
     (E ef ρκ σ next-aκ)]
    [(setk a next-aκ)
     (define next-σ (σ-join σ a v))
     (A (void) ρ next-σ next-aκ)]
    [(callcck e next-aκ)
     (callfunc v (list (σ-ref σ next-aκ)) ρ σ e next-aκ)]
    [(applyk applyexp '() e ρκ next-aκ)
     (define next-next-aκ (kaddr (σ-count σ)))
     (define κ (applyk applyexp (someval v) e ρκ next-aκ))
     (define next-σ (σ-join σ next-next-aκ κ))
     (E e ρκ next-σ next-next-aκ)]
    [(applyk applyexp (someval vf) _ _ next-aκ)
     (callfunc vf v ρ σ applyexp next-aκ)]
    [(callk call done (cons eh et) ρκ next-aκ)
     (define next-next-aκ (kaddr (σ-count σ)))
     (define κ (callk call (append done (list v)) et ρκ next-aκ))
     (define next-σ (σ-join σ next-next-aκ κ))
     (E eh ρκ next-σ next-next-aκ)]
    [(callk call done '() _ next-aκ)
     (match-define (cons vh vs) (append done (list v)))
     (callfunc vh vs ρ σ call next-aκ)]))

; forms an initial state from an expression
(define (inject e) (E e (env 0 '()) (hash (kaddr 0) (mtk)) (kaddr 0)))

(define (step ς)
  (match ς
    [(? E?) (step-eval ς)]
    [(? A?) (step-apply ς)]))

; iterates an initial state until fixpoint
(define (evaluate program)
  (define state0 (inject program))
  (define (run st)
    (define next (step st))
    (if (equal? next st) st (run next)))
  (run state0))

(define e evaluate)

; test suite?
#;
(list
 ; tests just functions doing function things, and also a free variable used.
 ; super simple, should complete in a state with (λ (a) a) as the value.
 (e '((λ (free) ((λ (d) d) ((λ (e) e) ((λ () free)))))
      ((λ (c) c) ((λ (b) b) (λ (a) a)))))
 ; smaller version of the last test
 (e '((λ (free) ((λ () free)))
      (λ (x) x)))
 ; testing simple function call and if expression and numbers
 ; returns 12
 (e ((λ (x) x) (if #f 3 12)))
 ; similar as the last test, but returns a singleton list of 12
 (e ((λ x x) (if #t 12 3)))
 )
