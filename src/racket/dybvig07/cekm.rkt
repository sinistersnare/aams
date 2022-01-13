#lang racket

; A CEK machine similar to that shown in figure 1 of
; Dybvig et al. 2007 "A Monadic Framework for Delimited Continuations"
;
; This is an implementation of the 4 basic operators given from the paper.
; It is modified, adding an environment, and a distinction between
; eval and apply states.
;
; It does not use redex-semantics directly, but it is inspired by the
; paper nonetheless.

; a delimited continuation prompt.
(struct promptv (p) #:transparent)
; a primitive function
(struct primv (p) #:transparent)
(define prims (hash 'add1 (primv (λ (n) (add1 n)))
                    'displayln (primv (λ (v) (displayln v)))
                    '+ (primv +)))

(define (prim? x) (member x (hash-keys prims)))

(define (atomic? x) (match x
                      [(or `(λ ,_ ,_) (? boolean?) (? number?)
                           (? prim?) (? promptv?) (? symbol?)) #t]
                      [_ #f]))


; state types
;; The 'meta'-continuation is the full continuation here,
;; called the 'sequence' in Dybvig 07.
;; The 'Continuation' itself is a simply the 'delimited context'
;; as shown in the paper.
(struct E (ctrl env kont meta) #:transparent)
(struct A (val kont meta) #:transparent)

(define (atomic-eval v ρ)
  (match v
    [`(λ ,_ ,_) `(clo ,v ,ρ)]
    [(? prim?) (hash-ref prims v)]
    [(? symbol?) (hash-ref ρ v)]
    ; numbers, prompts, etc. just get passed unchanged.
    [_ v]))

(struct mtκ () #:transparent)
(struct ifκ (et ef ρ κ) #:transparent)
(struct pushPromptκ (ebody ρ κ) #:transparent)
(struct pushSubContκ (ebody ρ κ) #:transparent)
(struct fnκ (done todo ρ κ) #:transparent)

(define (step-E st)
  (match-define (E ctrl ρ κ γ) st)
  (match ctrl
    [(? atomic? v) (A (atomic-eval v ρ) κ γ)]
    [`(if ,ec ,et ,ef) (E ec ρ (ifκ et ef ρ κ) γ)]
    ; just use gensym instead of keeping the next number around in the state.
    ; do the symbol->string->symbol dance so it gets interned and we can use eq?
    [`(newPrompt) (A (promptv (string->symbol (symbol->string
                                               (gensym 'prompt)))) κ γ)]
    ; right now, the second arg to pushPrompt is just a body
    ; to be executed in a non-standard way.
    ; This requires a special continuation frame.
    ; if we wanted to simply eval, we could require this to be a thunk,
    ; and worry about special work in the function call logic.
    [`(pushPrompt ,ep ,ebody) (E ep ρ (pushPromptκ ebody ρ κ) γ)]
    ; takes a 1-arg function as second argument, that arg is the cont obj.
    [`(withSubCont ,ep ,ef) (E ep ρ (fnκ '(withSubContκ) (list ef) ρ κ) γ)]
    ; reinstates the delim continuation eseq with value ev in the hole.
    ; could be simplified to just let eseq be represented as a function.
    ; TODO: I feel like this can be impld as a special case of fnκ...
    ;       But there may be some evaluation-order trickery im not thinking of?
    ;       unlikely because if we just impl sequences as functions then
    ;       eval-order would be regular... hmm...
    [`(pushSubCont ,eseq ,ebody) (E eseq ρ (pushSubContκ ebody ρ κ) γ)]
    [`(,ef ,es ...) (E ef ρ (fnκ '() es ρ κ) γ)]))

(define (step-A st)
  (match-define (A v outerκ γ) st)
  (match outerκ
    ; when current delimited context is empty, we must consult
    ; the Sequence to decide what to do next.
    [(mtκ)
     (match (γseq-get-next γ)
       [(cons newκ newγ) (A v newκ newγ)]
       ; if there is no next, return empty so its done
       [_ (A v (mtκ) (γseq-empty))])
     (match-define (cons newκ newγ) (γseq-get-next γ))
     (A v newκ newγ)]
    ; delimits the current context. v is a prompt.
    [(pushPromptκ ebody ρ κ)
     ; TODO: check this, I think κ is correct here, and not some other kont.
     (E ebody ρ (mtκ) (γseq-cons v (γseq-cons κ γ)))]
    ; Here, v is a sequence, and we use it to reinstate the continuation.
    [(pushSubContκ ebody ρ κ)
     (E ebody ρ (mtκ) (γseq-append v (γseq-cons κ γ)))]
    [(ifκ et ef ρ κ)
     (E (if (false? v) ef et) ρ κ γ)]
    [(fnκ all-done '() ρ κ)
     (match-define (cons f args) (append all-done (list v)))
     (match f
       ['withSubContκ
        ; here, v is a closure taking 1 argument
        ; we call the function giving it the delimited seq.
        (match-define `(,p (clo (λ (,k) ,ebody) ,ρ)) args)
        ; TODO: should the cons be before or after the delimit?
        ;       I feel like if prompts are not repeated it
        ;       should not matter semantically.
        (define before-γseq (γseq-before (γseq-cons κ γ) p))
        (define after-γseq (γseq-after γ p))
        (E ebody (hash-set ρ k before-γseq) (mtκ) after-γseq)]
       [`(clo (λ ,xs ,e) ,ρ)
        (E e (foldr (λ (x v h) (hash-set h x v)) ρ xs args) κ γ)]
       [(primv pf) (A (apply pf args) κ γ)])]
    [(fnκ done (cons next rest) ρ κ)
     (E next ρ (fnκ (append done (list v)) rest ρ κ) γ)]))

(define (step s)
  (match s
    [(? E?) (step-E s)]
    [(? A?) (step-A s)]
    [_ (error "wat")]))

; TODO: add a top-level prompt to the program so we can have call/cc?
; TODO: add top-level F-family functions for different usage?
;       -F- is withSubCont, I want -+, +-, and ++ (shift) too!
(define (inject e) (E e (hash) (mtκ) (γseq-empty)))

(define (run e0)
  (define injected (inject e0))
  (define (loop s)
    #;(pretty-print s)
    (define next (step s))
    (match next
      [(A _ (mtκ) (? γseq-empty?)) next]
      [_ (loop next)]))
  (loop injected))

(define (γseq? γ)
  (match γ
    [(or 'γε `(γp ,_ . ,_) `(γκ ,_ . ,_)) #t]
    [_ #f]))
(define (γseq-empty) 'γε)
(define (γseq-empty? seq) (match seq ['γε #t] [_ #f]))
(define (γseq-cons l r)
  (match l
    [(? promptv?) `(γp ,l . ,r)]
    [_ `(γκ ,l . ,r)]))

(define (γseq-append l r)
  (match l
    ['γε r]
    [`(γp ,ll . ,lr) `(γp ,ll . ,(γseq-append lr r))]
    [`(γκ ,ll . ,lr) `(γκ ,ll . ,(γseq-append lr r))]))

; the up-arrow delimit operator
(define (γseq-before γ needle)
  (match γ
    ['γε γ]
    [`(γp ,maybe . ,r) (if (eq? maybe needle) 'γε (γseq-before r needle))]
    [`(γκ ,l . ,r) `(γκ ,l . ,(γseq-before r needle))]))

; the down-arrow delimit operator
(define (γseq-after γ needle)
  (match γ
    ['γε γ]
    [`(γp ,maybe . ,r) (if (eq? maybe needle) r (γseq-after r needle))]
    [`(γκ ,l . ,r) (γseq-after r needle)]))

; when the current delimited context is empty, we need to traverse
; the sequence to get the next context (this is underflow behavior).
(define (γseq-get-next γold)
  (match γold
    [`γε '()]
    [`(γp ,_ . ,r) (γseq-get-next r)]
    [`(γκ ,κ . ,γ) (cons κ γ)]))


;(cons 'a (reset (cons 'b (shift f (cons 1 (f (f (cons 'c '()))))))))
