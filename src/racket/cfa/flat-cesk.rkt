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
(struct kaddr (e ρ) #:transparent)

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
(struct mtk ktype ())
(struct callk ktype (call done todo ρ aκ))

; primitive functions, implemented by the implementation
(struct prim (op))
(define prims
  (hash '+ (prim +)))

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
    [else #f]))

; STORE
;
; join in the concrete semantics is defined as
; a simple extension
(define (σ-join σ aκ κ)
  (hash-set σ aκ κ))
(define (σ-ref σ a)
  (hash-ref σ a))

; ENVIRONMENT
;
; To make a new environment, you simply append
; the newest call to the stack, and increment the address
(define (ρ-new call ρ)
  (match-define (env n call-list) ρ)
  (env (add1 n) '() #;(cons call call-list)))

; finds all variables that do not have a binding
; inside of the expression.
;
; returns a list of all unbound vars.
(define (find-free-vars e bound)
  (match e
    [`(,(? λ-start?) (,xs ...) ,eb)
     (find-free-vars eb (foldl (λ (x s) (set-add s x)) bound xs))]
    [`(,es ...)
     (foldl (λ (e t) (append t (find-free-vars e bound))) '() es)]
    [(? symbol?)
     (if (set-member? bound e) '() (list e))]
    [_ (error (format "We do not cover the case of '~a'" e))]))

(define (atomic-eval ς)
  (match-define (E e ρ σ _) ς)
  (match e
    [(? λ?) (closure e ρ)]
    [(? symbol?) (σ-ref σ (baddr e ρ))]))

(define (step-eval ς)
  (match-define (E eς ρ σ aκ) ς)
  ;(displayln (cons eς ρ))
  (match eς
    [(? atomic?)
     (define v (atomic-eval ς))
     (A v ρ σ aκ)]
    [`(,ef ,es ...)
     (define next-aκ (kaddr ef ρ))
     (define κ (callk eς '() es ρ aκ))
     (define next-σ (σ-join σ next-aκ κ))
     (E ef ρ next-σ next-aκ)]))

(define (step-apply ς)
  (match-define (A v ρ σ aκ) ς)
  ;(displayln v)
  (define κς (σ-ref σ aκ))
  (match κς
    [(mtk) ς]
    [(callk call done todo ρκ next-aκ)
     (match todo
       ['() ; done, time to execute call
        (match-define (cons head arg-vals) (append done (list v)))
        (match head
          [(closure `(,_ (,xs ...) ,eb) ρλ)
           (define next-ρ (ρ-new call ρ))
           (define arg-addresses (map (λ (x) (baddr x next-ρ)) xs))
           (define arg-bindings (map cons arg-addresses arg-vals))
           (define free-vars (find-free-vars `(λ ,xs ,eb) (set)))
           (define free-vals (map (λ (x) (σ-ref σ (baddr x ρλ))) free-vars))
           (define free-addresses (map (λ (x) (baddr x next-ρ)) free-vars))
           (define free-bindings (map cons free-addresses free-vals))
           (define all-bindings (append arg-bindings free-bindings))
           (define next-σ (foldl (λ (bnd res) (σ-join res (car bnd) (cdr bnd)))
                                 σ all-bindings))
           (E eb next-ρ next-σ next-aκ)])]
       [(cons eh et) ; more args left to evaluate.
        (define next-next-aκ (kaddr eh ρκ))
        (define κ (callk call (append done (list v)) et ρκ next-aκ))
        (define next-σ (σ-join σ next-next-aκ κ))
        (E eh ρκ next-σ next-next-aκ)])]))

; forms an initial state from an expression
(define (inject e) (E e (env 0 '()) (hash (kaddr 0 0) (mtk)) (kaddr 0 0)))

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
 (e '((λ (free) ((λ () free)))
      (λ (x) x)))
 )
