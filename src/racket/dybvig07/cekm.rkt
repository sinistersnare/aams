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

;; I used this document for try/catch impl: https://gist.github.com/sebfisch/2235780


; a mutable cell, needs the current value for Get and the continuation for Set.
(struct mutcellv (v p) #:transparent)
; a delimited continuation prompt.
(struct promptv (p) #:transparent)
; a closure value, lambda × environment
(struct clov (λ ρ) #:transparent)
; a primitive function
(struct primv (p) #:transparent)
(define prims (hash 'add1 (primv (λ (n) (add1 n)))
                    'displayln (primv (λ (v) (displayln v)))
                    '+ (primv +)
                    'makeCell (primv mutcellv)
                    'GetState (primv mutcellv-v)
                    'GetStatePrompt (primv mutcellv-p)))

(define (prim? x) (member x (hash-keys prims)))

; literals that are atomic and can be atomically evaluated.
(define (atomic? x) (match x
                      [(or `(λ ,_ ,_) (? boolean?) (? number?) (? string?) (? symbol?)) #t]
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
;; The 'Continuation' itself is a simply the 'delimited context'
;; as shown in the paper.
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

(struct mtκ () #:transparent)
(struct ifκ (et ef ρ κ) #:transparent)
(struct pushPromptκ (ebody ρ κ) #:transparent)
(struct pushSubContκ (ebody ρ κ) #:transparent)
(struct fnκ (done todo ρ κ) #:transparent)

; _should_ return the number 8... Not a cell or anything else.
#; ; doesnt work because the prompt is lost after the argument is evaluated.
   ; so we need to wrap the whole call/state with a pushPrompt...
'((λ (cell)
    ((λ (_) (+ 1 (GetState cell)))
     ((λ (cellprompt) (withSubCont cellprompt (λ (_) (makeCell 7 cellprompt))))
      (%%GetStatePrompt cell))))
  ((λ (prompt)
     (pushPrompt prompt
                 (makeCell 5 prompt)))
   (newPrompt)))
#;
'((λ (cell) ((λ (_) (+ 1 (GetState cell)))
             (SetCell cell 7)))
  (makeCell 5))

(define (step-E st)
  (match-define (E ctrl ρ κ γ) st)
  #;(pretty-display `(ctrl: ,ctrl atomic? ,(atomic? ctrl)))
  (match ctrl
    [(? atomic? v) (A (atomic-eval v ρ) κ γ)]
    [`(if ,ec ,et ,ef) (E ec ρ (ifκ et ef ρ κ) γ)]
    ; eval is the initial value of the state
    ; ebody is a lambda that takes an argument which is the variable that holds the state.
    ; inside of the ebody, (GetState ,var) and (SetState ,var ,newVal) can be used to get/set.
    ; GetState is impld as a primitive function! nice!
    [`(call/state ,initval ,ebody)
     (define promptname (gensym 'p))
     (define kname (gensym 'κ))
     (E `((λ (,promptname)
            (pushPrompt
             ,promptname
             (,ebody (makeCell ,initval ,promptname))))
          (newPrompt))
        ρ κ γ)
     #;
     (E `(,ebody
          ((λ (,promptname)
             (pushPrompt ,promptname
                         (makeCell ,initval ,promptname)))
           (newPrompt)))
        ρ κ γ)]
    [`(SetState ,cell ,newval)
     (define cellpromptname (gensym 'cellκ))
     (E `((λ (,cellpromptname)
            (withSubCont ,cellpromptname (λ (_) (makeCell ,newval ,cellpromptname))))
          (%%GetStatePrompt ,cell))
        ρ κ γ)]
    ; just use gensym instead of keeping the next number around in the state.
    ; do the symbol->string->symbol dance so it gets interned and we can use eq?
    [`(newPrompt) (A (promptv (string->symbol (symbol->string
                                               (gensym 'prompt)))) κ γ)]

    ; throw and try are syntax transformers.
    ; they just reinterpret the code into more code.
    ;; TODO: make a %%CUR-EXC-PROMPT at the top level so top-level throw works...?
    [`(throw ,e)
     (define handlervar (gensym 'handler))
     (E `(withSubCont %%CUR-EXC-PROMPT
                      (λ (%%_k) (λ (,handlervar) (,handlervar ,e))))
        ρ κ γ)]
    [`(try ,etry ,ecatch)
     ; if etry throws then the binding never materializes because control is
     ; thrown to the handler. If it does not throw, then the inner 1-unused-arg
     ; lambda *is* returned, so the handler (unused arg)
     ; is disregarded inside of it.
     (E `(((λ (%%CUR-EXC-PROMPT)
             (pushPrompt %%CUR-EXC-PROMPT ((λ (%%temp) (λ (_h) %%temp))
                                           ,etry)))
           (newPrompt))
          ,ecatch)
        ρ κ γ)]
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
    ;       That is, get rid of pushSubCont and just do (κ val) call syntax
    ;       like call/cc.
    ;       But there may be some evaluation-order trickery im not thinking of?
    ;       unlikely because if we just impl sequences as functions then
    ;       eval-order would be regular... hmm...
    [`(pushSubCont ,eseq ,ebody) (E eseq ρ (pushSubContκ ebody ρ κ) γ)]
    ; impl let as a simple shorthand for function calling.
    ; just for convenience.
    [`(let ([,xs ,es] ...) ,ebody)
     (E `((λ ,xs ,ebody) . ,es) ρ κ γ)]
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
        (match-define `(,p ,(clov `(λ (,k) ,ebody) ρ)) args)
        ; TODO: should the cons be before or after the delimit?
        ;       I feel like if prompts are not repeated it
        ;       should not matter semantically.
        (define before-γseq (γseq-before (γseq-cons κ γ) p))
        (define after-γseq (γseq-after γ p))
        (E ebody (hash-set ρ k before-γseq) (mtκ) after-γseq)]
       [(clov `(λ ,xs ,e) ρ)
        (when (not (= (length xs) (length args)))
          (pretty-display `(incorrect-number-of-args!
                            expected: ,(length xs)
                            given: ,(length args)
                            for function (λ ,xs ,e)))
          (raise 'badargs))
        (E e (foldr (λ (x v h) (hash-set h x v)) ρ xs args) κ γ)]
       [(primv pf) (A (apply pf args) κ γ)]
       [_ (pretty-display f) (raise 'unknown-f)])]
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

(define (inject e) (E e starting-env (mtκ) (γseq-empty)))

(define (run e0)
  (define injected (inject e0))
  (define (loop s)
    #;(pretty-print s)
    (define next (step s))
    (match next
      [(A _ (mtκ) (? γseq-empty?)) next]
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
         [(A _ (mtκ) (? γseq-empty?)) next]
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

#;
(require racket/control)
#;
(let ([pout (new-prompt)]
      [pin (new-prompt)])
  (+ 1 (reset-at pout
                 (+ 1 2 (shift-at pout k 4))))
  #;
  (+ 1 (reset-at
        pout
        (shift-at
         pout kout
         (+ 1 2
            (reset-at pin (shift-at pin kin (kout 3))))))))


;; simple examples of straight DC
#;
(run '((λ (p) (pushPrompt p (withSubCont p (λ (k) (+ 1 (pushSubCont k 5)))))) (newPrompt)))
#;
(run '((λ (p) (pushPrompt p (+ 1 (withSubCont p (λ (k) (+ 2 1)))))) (newPrompt)))
;; TODO: add examples of try/catch
;; TODO: add examples of mutation
