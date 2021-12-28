#lang racket

; This machine is a CESKM machine
; Control, Env, Store, Kontinuation, MetaKontinuation
; From Danvy, Filinski 1990: Abstracting Control

; The goal is to implement shift/reset semantics.
; The machine isnt a classic AM, so its not big or small, but im gonna try to shoe-horn it in anyways.
; if anything it would be a big step....? Cause it evaluates in terms of evaluation.

(struct E (ctrl env kont meta) #:transparent)
(struct A (val kont meta) #:transparent)
(struct condκ (et ef ρ κ) #:transparent)
(struct escapeκ (κ) #:transparent)
(struct delimκ (κ) #:transparent)
(struct delimγ (κ γ) #:transparent)
(struct shiftκ () #:transparent)
(struct resetκ () #:transparent)
(struct resetγ (κ γ) #:transparent)
(struct fnκ (done todo ρ κ) #:transparent)
(struct argκ (v κ) #:transparent)

(struct primv (p) #:transparent)

(define prims (hash 'add1 (primv (λ (n) (add1 n)))
                    'displayln (primv (λ (v) (displayln v)))
                    '+ (primv +)))
(define (prim? x) (member x (hash-keys prims)))

(define (atomic? x) (match x
                      [(or `(λ ,_ ,_) (? boolean?) (? number?)
                           (? prim?) (? symbol?)) #t]
                      [_ #f]))
(define (atomic-eval v ρ)
  (match v
    [`(λ ,_ ,_) (cons v ρ)]
    [(? prim?) (hash-ref prims v)]
    [(? symbol?) (hash-ref ρ v)]
    [_ v]))

; γ should be stored in continuation frames so it can be restored???
(define (step-E st)
  (match-define (E ctrl ρ κ γ) st)
  (match ctrl
    ; control is non-atomic, evaluate syntax.
    ;[`(,(? prim? π) ,e) (E e ρ `(primκ π κ) γ)]
    [(? atomic? v) (A (atomic-eval v ρ) κ γ)]
    [`(if ,ec ,et ,ef) (E ec ρ (condκ et ef ρ κ) γ)]
    [`(ε ,k ,e) (E e (hash-set ρ k (escapeκ κ)) κ γ)]
    [`(ξ ,k ,e) (E e (hash-set ρ k (delimκ κ)) (shiftκ) γ)]
    [`(<> ,e) (E e ρ (resetκ) (resetγ κ γ))]
    [`(,ef ,es ...) (E ef ρ (fnκ '() es ρ κ) γ)]))

(define (step-A st)
  (match-define (A v outerκ γ) st)
  (match outerκ
    ['mtκ st]
    [(condκ et ef ρ κ)
     (if (false? v)
         (E ef ρ κ γ)
         (E et ρ κ γ))]
    [(fnκ almost-all-done '() ρ κ)
     (match-define (cons f args) (append almost-all-done (list v)))
     (match f
       [(cons `(λ ,xs ,e) ρ)
        (E e (foldr (λ (x v h) (hash-set h x v)) ρ xs args) κ γ)]
       [(primv pf) (A (apply pf args) κ γ)]
       ; only the first arg is used for continuations.
       [(escapeκ innerκ) (A (car args) innerκ γ)]
       [(delimκ innerκ) (A (car args) innerκ (delimγ κ γ))])]
    [(fnκ done (cons next rest) ρ κ)
     (E next ρ (fnκ (append done (list v)) rest ρ κ) γ)]
    [(fnκ '() e2 ρ κ)
     (E e2 ρ (argκ v κ) γ)]
    [(or (shiftκ) (resetκ))
     (match-define (or (resetγ innerκ innerγ) (delimγ innerκ innerγ)) γ)
     (A v innerκ innerγ)]))

(define (step s)
  (match s
    [(? E?) (step-E s)]
    [(? A?) (step-A s)]
    [_ (error "WAT")]))

(define (inject e) (E e (hash) 'mtκ 'mtγ))

(define (run e0)
  ; TODO: is the mtγ metacontinuation correct? Or will it hit something weird...
  (define injected (inject e0))
  (define (loop s)
    ;(pretty-display s)
    (define next (step s))
    (if (equal? s next) next (loop next)))
  (loop injected))

(define (run-for s n)
  (match n
    [0 s]
    [n (run-for (step s) (- n 1))]))

(define (run-print-range s start end)
  (match (cons start end)
    [(cons 0 0) s]
    [(cons 0 n)
     (pretty-print s)
     (run-print-range (step s) 0 (- n 1))]
    [(cons nstart nend)
     (run-print-range (step s) (- nstart 1) (- nend 1))]))


'((lambda (flip fail choice triple) (<> (displayln (triple 10 15))))
  (lambda () (ξ c (begin (c #t) (c #f) (fail)))))
