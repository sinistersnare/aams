#lang racket

(provide run)

(require racket/struct)
; A CEK machine similar to that shown in figure 1 of
; Dybvig et al. 2007 "A Monadic Framework for Delimited Continuations"
;
; This is an implementation of the 4 basic operators given from the paper.
; It is modified, adding an environment, and a distinction between
; eval and apply states.
;
; It does not use redex-semantics directly, but it is inspired by the
; paper nonetheless.

;; I used this document for try/catch impl: https://gist.github.com/sebfisch/2235780


; effect handler object, used as evidence when performing effects.
; the prompt is used to find which handler to get to
; and the handlers object is a hash to search for the handler.
(struct handlerv (prompt handlers) #:transparent)
(struct handleropv (i) #:transparent)
; a delimited continuation prompt.
(struct promptv (p) #:transparent)
; a closure value, lambda × environment
(struct clov (λ ρ) #:transparent
  ; a pretty printer so the whole environment isnt written out, just the keys.
  #:methods gen:custom-write [(define write-proc
                                (make-constructor-style-printer
                                 (λ (obj) 'closure)
                                 (λ (o) (list (clov-λ o)
                                              (hash-keys (clov-ρ o))))))])
; a primitive function
(struct primv (p) #:transparent)
(define prims (hash 'displayln (primv (λ (v) (displayln v)))
                    'add1 (primv add1)
                    '+ (primv +)
                    'MakeHandler (primv (λ (prompt . handlers)
                                          (handlerv prompt (apply vector handlers))))
                    'HandlerPrompt (primv handlerv-prompt)
                    'HandlerGet (primv (λ (h i) (vector-ref (handlerv-handlers h)
                                                            (handleropv-i i))))
                    'MakeOp (primv handleropv)))

(define (prim? x) (member x (hash-keys prims)))

; literals that are atomic and can be atomically evaluated.
(define (atomic? x) (match x
                      [(or `(quote ,_) `(λ ,_ ,_)
                           (? boolean?) (? number?)
                           (? string?) (? symbol?)) #t]
                      [_ #f]))

;; TODO:
;; impl mutation
;; impl amb, or backtracking search
;;
;; hypothesis: Copying and reinstating happens a lot of times...
;; could it be done smarter?
;; if we know its gonna be done, could we use assignment instead
;; of complex stack maneuvers?

;; maybe if we have a `reset`/`pushPrompt` and we know there is a `shift`/`withSubCont` coming,
;; we dont execute any of the inner bits? Because theyre just gonna be aborted later... Maybe we
;; evaluate it then? And then if the continuation is never reinstated we would have saved some work!
;; like (+ 1 (reset (+ 2 3 (shift k (if (rand) (k 4) 4)))))
;; Depending on (rand), this could return 5 or 10. Whats the point of pre-computing (+ 2 3 [])
;; if we may not actually reinstantiate it
;;
;; I think this should be done only if we know that reset will be called,
;; but are just unsure if the cont will be reinstated.

; state types
;; The 'meta'-continuation is the full continuation here,
;; called the 'sequence' in Dybvig 07.
;; The 'Continuation' itself is a simply the 'delimited context' from the paper.
(struct E (ctrl env kont meta) #:transparent)
(struct A (val kont meta) #:transparent)

(define (atomic-eval v ρ)
  (match v
    [`(λ ,_ ,_) (clov v ρ)]
    [(? prim?) (hash-ref prims v)]
    [(? symbol?) (hash-ref ρ v (λ () (pretty-display `(cant find ,v in ,ρ))
                                  (raise 'no-symbol!)))]
    ; numbers, strings, prompts, etc. just get passed unchanged.
    [_ v]))

(struct ifκ (et ef ρ κ) #:transparent)
(struct pushPromptκ (ebody ρ κ) #:transparent)
(struct withSubContκ (ep ef ρ κ) #:transparent)
(struct pushSubContκ (ebody ρ κ) #:transparent)
(struct fnκ (done todo ρ κ) #:transparent)

#;
(match '(withHandler ([throw (λ (x k) x)] [get (λ (x k) (k 1))])
                     (+ 1000 (perform throw (+ 1 (perform get 3)))))
  ['(withHandler ([,ops ,hs] ...) ,ebody) 'good]
  [else 'bad])

(define (step-E st)
  (match-define (E ctrl ρ κ γ) st)
  #;(pretty-display `(ctrl: ,ctrl atomic? ,(atomic? ctrl)))
  (match ctrl
    [(? atomic? v) (A (atomic-eval v ρ) κ γ)]
    ; just use gensym instead of keeping the next number around in the state.
    ; do the symbol->string->symbol dance so it gets interned and we can use eq?
    [`(newPrompt) (A (promptv (string->symbol (symbol->string
                                               (gensym 'prompt)))) κ γ)]
    ; right now, the second arg to pushPrompt is just a body
    ; to be executed in a non-standard evaluation order.
    ; This requires a special continuation frame.
    ; if we wanted to simply eval, we could require this to be a thunk,
    ; and worry about special work in the function call logic.
    [`(pushPrompt ,ep ,ebody) (E ep ρ (pushPromptκ ebody ρ κ) γ)]
    ; takes a 1-arg function as second argument, that arg is the cont obj.
    [`(withSubCont ,ep ,ef) (E ep ρ (withSubContκ '∅ ef ρ κ) γ)]
    ; reinstates the delim continuation eseq with value ev in the hole.
    ; could be simplified to just let eseq be represented as a function.
    [`(pushSubCont ,eseq ,ebody) (E eseq ρ (pushSubContκ ebody ρ κ) γ)]
    ; elam is a 1-arg lambda, which is called given the handler reference
    ; for use when performing operations.
    ; used like
    #; (call/handler ([throw (λ (_ x) x)] [get (λ (k) (k 4))])
                     (λ (m) (+ 1 (perform throw m (perform get m)))))
    #; (withHandler (...) (+ 1 (perform throw (perform get))))
    [`(call/handler ([,ops ,fs] ...) ,elam)
     (define promptname (gensym 'p))
     (define opbinds (map (λ (op i) `[,op (MakeOp ,i)]) ops (range (length ops))))
     (E `(let ([,promptname (newPrompt)] . ,opbinds)
           (pushPrompt ,promptname (,elam (MakeHandler ,promptname . ,fs))))
        ρ κ γ)]
    ; TODO: It seems Biernacki et al 2019,
    ;                Brachthauser and Schuster 2017, and
    ;                Zhang and Myers 2019 all cover
    ;       'lexical effect handlers using delimited control'. Look at those?
    ;       See the last bullet point before Fig1 in 'Effect Handlers, Evidently'
    [`(perform ,eop ,eh ,args ...)
     ; handlers have +F+ semantics, so we can nest `perform` calls and we can
     ; reinstantiate handlers outside of their original context.
     (define kname (gensym 'k))
     (define opname (gensym 'op))
     (define hname (gensym 'h))
     (define kargname (gensym 'karg))
     (define promptvar (gensym 'promptvar))
     (E `(let ([,opname ,eop] [,hname ,eh])
           (let ([,promptvar (HandlerPrompt ,hname)])
             (withSubCont
              ,promptvar
              (λ (,kname)
                (pushPrompt
                 ,promptvar
                 ((HandlerGet ,hname ,opname)
                  (λ (,kargname) (pushPrompt
                                  ,promptvar
                                  (pushSubCont ,kname ,kargname))) . ,args))))))
        ρ κ γ)]
    [`(if ,ec ,et ,ef) (E ec ρ (ifκ et ef ρ κ) γ)]
    ; impl let as a simple shorthand for function calling... for convenience!
    [`(let ([,xs ,es] ...) ,ebody)
     (E `((λ ,xs ,ebody) . ,es) ρ κ γ)]
    [`(,ef ,es ...) (E ef ρ (fnκ '() es ρ κ) γ)]))

(define (step-A st)
  (match-define (A v outerκ γ) st)
  #;(pretty-display `(dealing-with ,v))
  (match outerκ
    ; when current delimited context is empty, we must consult
    ; the Sequence to decide what to do next.
    ['κε
     (match (γseq-get-next γ)
       [(cons newκ newγ) (A v newκ newγ)]
       ; if there is no next, return empty so its done
       [_ (A v 'κε (γseq-empty))])
     (match-define (cons newκ newγ) (γseq-get-next γ))
     (A v newκ newγ)]
    ; delimits the current context. v is a prompt.
    [(pushPromptκ ebody ρ κ)
     #;(pretty-display `(placing-prompt ,v))
     (E ebody ρ 'κε (γseq-cons v (γseq-cons κ γ)))]
    [(withSubContκ '∅ ef ρ κ)
     (E ef ρ (withSubContκ v '∅ ρ κ) γ)]
    [(withSubContκ p '∅ ρ κ)
     ; here, v is a closure taking 1 argument
     ; we call the function giving it the delimited seq.
     (match-define (clov `(λ (,k) ,ebody) ρ) v)
     #;(pretty-display `(splitting ,p ,γ))
     (define before-γseq (γseq-cons κ (γseq-before γ p)))
     (define after-γseq (γseq-after γ p))
     (E ebody (hash-set ρ k before-γseq) 'κε after-γseq)]
    ; Here, v is a sequence, and we use it to reinstate the continuation.
    [(pushSubContκ ebody ρ κ)
     (E ebody ρ 'κε (γseq-append v (γseq-cons κ γ)))]
    [(ifκ et ef ρ κ)
     (E (if (false? v) ef et) ρ κ γ)]
    [(fnκ all-done '() ρ κ)
     (match-define (cons f args) (append all-done (list v)))
     (match f
       [(clov `(λ ,xs ,e) ρ)
        (when (not (= (length xs) (length args)))
          (pretty-display `(incorrect-number-of-args!
                            expected: ,(length xs)
                            given: ,(length args)
                            for function (λ ,xs ,e)))
          (raise 'badargs))
        (E e (foldr (λ (x v h) (hash-set h x v)) ρ xs args) κ γ)]
       [(primv pf) (A (apply pf args) κ γ)]
       [_ (pretty-display `(not-given-a-function ,f)) (raise 'unknown-f)])]
    [(fnκ done (cons next rest) ρ κ)
     (E next ρ (fnκ (append done (list v)) rest ρ κ) γ)]))

(define reifys
  (hash 'reify (clov `(λ (k) (λ (v) (pushSubCont k v))) (hash))
        'reifyP (clov `(λ (p k) (λ (v) (pushPrompt p (pushSubCont k v)))) (hash))))
(define starting-env
  (hash
   'reify (hash-ref reifys 'reify)
   'reifyP (hash-ref reifys 'reifyP)
   '-F- (clov `(λ (p f) (withSubCont p (λ (k) (f (reify k))))) reifys)
   '-F+ (clov `(λ (p f) (withSubCont p (λ (k) (f (reifyP p k))))) reifys)
   '+F- (clov `(λ (p f) (withSubCont p (λ (k) (pushPrompt p (f (reify k)))))) reifys)
   '+F+ (clov `(λ (p f) (withSubCont p (λ (k) (pushPrompt p (f (reifyP p k)))))) reifys)))

; wraps a program in infrastructure, allowing call/cc to be used.
(define (wrap e)
  `((λ (p0)
      (pushPrompt
       p0
       ((λ (withCont)
          ((λ (reifyA)
             ((λ (call/cc) ,e)
              (λ (f) (withCont (λ (k) (pushSubCont k (f (reifyA k))))))))
           (λ (k) (λ (v) (withCont (λ (_) (pushSubCont k v)))))))
        (λ (e) (withSubCont p0 (λ (k) (pushPrompt p0 (e k))))))))
    (newPrompt)))

(define (step s)
  (match s
    [(? E?) (step-E s)]
    [(? A?) (step-A s)]
    [_ (raise "wat")]))

(define (inject e) (E e (hash) #;starting-env 'κε (γseq-empty)))

(define (run e0)
  (define injected (inject e0))
  (define (loop s)
    #;(pretty-print s)
    (define next (step s))
    (match next
      [(A _ 'κε (? γseq-empty?)) next]
      [_ (loop next)]))
  (loop injected))

(define (run-steps e0)
  (define s0 (inject e0))
  (define (loop s)
    (define got (string-trim (read-string 2)))
    (cond
      [(eq? got "p")
       (pretty-display s)
       (loop s)]
      [(eq? got "q")
       s]
      [else
       (define next (step s))
       (match next
         [(A _ 'κε (? γseq-empty?)) next]
         [_ (loop next)])]))
  (loop s0))

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
(define/contract (γseq-before γ needle)
  (-> γseq? promptv? γseq?)
  (match γ
    ; pretty sure we should raise here, if we are
    ; looking for a prompt that doesn't exist (anymore possibly).
    ['γε (raise `(needle-not-found! ,needle))]
    [`(γp ,maybe . ,r) (if (eq? maybe needle)
                           'γε
                           `(γp ,maybe . ,(γseq-before r needle)))]
    [`(γκ ,l . ,r) `(γκ ,l . ,(γseq-before r needle))]))

; the down-arrow delimit operator
(define/contract (γseq-after γ needle)
  (-> γseq? promptv? γseq?)
  (match γ
    ; pretty sure we should raise here, if we are
    ; looking for a prompt that doesn't exist (anymore possibly).
    ['γε (raise `(needle-not-found! ,needle))]
    [`(γp ,maybe . ,r) (if (eq? maybe needle) r (γseq-after r needle))]
    [`(γκ ,l . ,r) (γseq-after r needle)]))

; when the current delimited context is empty, we need to traverse
; the sequence to get the next context (this is underflow behavior).
; pop all prompts off the stack while looking for the next continuation.
(define (γseq-get-next γold)
  (match γold
    [`γε '()]
    [`(γp ,p . ,r) (γseq-get-next r)]
    [`(γκ ,κ . ,γ) (cons κ γ)]))


; TODO:
; Small examples to see how an AAM would react
; Concrete semantics LaTeX
; start work on AAM in Racket
; AAM in LaTeX
