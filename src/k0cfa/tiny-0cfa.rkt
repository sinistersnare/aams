#lang racket

(provide optimize)

(require (only-in racket/hash hash-union))

; the file should be able to be swapped out more or less per lattice-type.
; a really shitty and unsafe type-clas system hahaha
(require (only-in "abstract-type-lattice.rkt"
                  join-value bottom avalue
                  abstract-+ abstract-car abstract-cdr abstract-if abstract-app
                  make-abstract avalue? abstractify))

(require (only-in "utils.rkt"
                  state abstraction? concrete-value?
                  appf addf letf iff carf cdrf))

; a [k=0]-CFA based on the tiny-scheme-cek.rkt
; a CFA is an abstract interpretation, so we take the semantics of
; the tiny-scheme-cek, and we lift it up to the abstract
; this way we can guarantee termination of the interpreter.

; so, whats the difference between the concrete machine in tiny-scheme-cek.rkt
; and the abstract machine here? Well, the abstract machine takes a state,
; and returns a set of states reachable from the given.
; Also, the store is globally available, divorced from the state.
; this reduces algorithmic complexity.

; use a global store for continuation values.
; this is separated out from the value store for ease of use mostly
; but if call/cc gets implemented, we may need to combine them
; the keys are addresses still, but addresses are not the continuations
; themselves, they are the syntactic point in the program that they are found at.
; this will prevent an infinite loop from crippling program execution.
(define kstore (make-hash))

; the kstore has the same lattice as the store.
; a position is either uninhabited (bottom, so we wont be seeing it,
; unless there is a bug, a value, or top, if there are multiple inhabitants.
(define (update-kstore ctrl kont)
  (hash-update!
   ; the syntactic point (the control) is the address.
   ; simple and clean!
   kstore ctrl
   (λ (storage) (set-add storage kont))
   set)
  ctrl)

; use a global store of values, separated from the state.
; When we call `evaluate` the store is reset.
; this is a mapping from an address to an abstract set of values
; which overapproximates of the possible concrete values.
; Addresses are just the values though, so we dont need an environment rn.
(define store (make-hash))

; the store is a mapping from addr -> Value
; where Value is a n-tuple where n is the amount of values there are.
; so we have bool,int, and abstraction values now,
; so (bool, int, abstraction). But its more than that,
; we need to abstract it so it can efficiently store multiple values.
; becauase idk shit about this shit, im gonna keep it simple
; the tuple values can either be bottom, a single value, or top.
; except for the syntactic abstractions, which will be a list.
; bottom of it being empty, and no TOP... maybe itll work!
(define (update-store bnd)
  (match-define (cons name val) bnd)
  (hash-update!
   store name
   (λ (storage) (join-value storage val))
   ; empty 3 tuple to start.
   ; bottom is an empty list
   ; top is the symbol 'TOP.
   ; and a value is the value... easy to figure out! Who needs well typed sum types!
   bottom))

; this steps when the control is an atomic value
; so it needs to check the continuation to see what to do next.
(define (step-value ctrl kont)
  #;(displayln `(in-step-value: ,kont))
  (match kont
    [(== (set)) (raise 'no-kont-how????)]
    ['mt '()]
    [`(appf ,evald-incomplete () ,next-kaddr)
     (define evald (reverse (cons ctrl evald-incomplete)))
     (abstract-app evald next-kaddr update-store)]
    [`(appf ,evald-incomplete (,next ,rest ...) ,next-kaddr)
     (define evald (cons ctrl evald-incomplete))
     (define nkaddr (update-kstore ctrl (appf evald rest next-kaddr)))
     (list (state next nkaddr))]
    [`(addf ,evald-incomplete () ,next-kaddr)
     (abstract-+ (cons ctrl evald-incomplete) next-kaddr)]
    [`(addf ,evald-incomplete (,next ,rest ...) ,next-kaddr)
     (define evald (cons ctrl evald-incomplete))
     (define nkaddr (update-kstore ctrl (addf evald rest next-kaddr)))
     (list (state next nkaddr))]
    [`(iff ,et ,ef ,next-kaddr)
     (abstract-if ctrl et ef next-kaddr)]
    [`(letf ,name ,body ,next-kaddr)
     (update-store (cons name ctrl))
     (list (state body next-kaddr))]
    [`(carf ,next-kaddr)
     (abstract-car ctrl next-kaddr)]
    [`(cdrf ,next-kaddr)
     (abstract-cdr ctrl next-kaddr)]))

(define (step st)
  (match-define `(state ,ctrl ,kaddr) st)
  #;(displayln `(ctrl: ,ctrl))
  (match ctrl
    [(? avalue?)
     (foldl append '() (set-map (hash-ref kstore kaddr) (λ (k) (step-value ctrl k))))]
    [`(+ ,es ...)
     #;(displayln 'add)
     (define nkaddr (update-kstore ctrl (addf '() es kaddr)))
     (list (state (make-abstract 0) nkaddr))]
    [`(if ,econd ,et ,ef)
     #;(displayln 'if)
     (define nkaddr (update-kstore ctrl (iff et ef kaddr)))
     (list (state econd nkaddr))]
    [`(car ,xs)
     (define nkaddr (update-kstore ctrl (carf kaddr)))
     (list (state xs nkaddr))]
    [`(let (,name ,exp) ,body)
     #;(displayln 'let)
     (define nkaddr (update-kstore ctrl (letf name body kaddr)))
     (list (state exp nkaddr))]
    [`(,ef ,es ...)
     #;(displayln `(appl ,ef and ,es))
     ;(displayln `(currentk: ,(hash-ref kstore kaddr)))
     (define nkaddr (update-kstore ctrl (appf '() es kaddr)))
     (list (state ef nkaddr))]
    [(? symbol?)
     #;(displayln 'sym)
     (list (state (hash-ref store ctrl) kaddr))]))

(define (inject e) (state e 'mt))

(define (evaluate e)
  (set! store (make-hash))
  (set! kstore (make-hash (list (cons 'mt (set 'mt)))))
  ; go takes a list of states to process and a hash of reached states (and where they lead)
  ; and returns a set of reached states, and where they lead (like an edge-list).
  (define (go states reached)
    (define new-reached (make-hash (map (lambda (st) (cons st (step st))) states)))
    (define union-reached (hash-union reached new-reached))
    (define todo-states (dropf (append-map identity (hash-values new-reached))
                               (lambda (s) (hash-has-key? union-reached s))))
    (if (empty? todo-states) union-reached (go todo-states union-reached)))
  (define cfg (go (list (inject (abstractify e))) (hash)))
  (list cfg store kstore))

(define (optimize-plus exp cfg store kstore)
  (define (go e)
    (define (guaranteed-number? e)
      (match e
        [(? concrete-value? val)
         (match val
           [(? number?) #t]
           [else #f])]
        ; maybe we could combine this with an analysis on which branch is taken?
        ; right now i always take both, so we dont care.
        [`(if ,_ ,et ,ef) (and (guaranteed-number? et) (guaranteed-number? ef))]
        [`(+ ,es ...) (andmap guaranteed-number? es)]
        [`(let ,_ ,letbody) (guaranteed-number? letbody)]
        [`(,ef ,es ...)
         (define k-at-appl (search-for-ks cfg kstore (abstractify e)))
         (assert (= (length k-at-appl) 1) 'k-at-appl) ; idk what to do in this case yet.
         (define ctrls-with-k (get-ctrls-with-k cfg kstore (car k-at-appl)))
         (define relevant (filter avalue? ctrls-with-k))
         (assert (= (length relevant) 1) 'relevant) ; idk what to do in this case yet.
         (equal? (avalue number? (set)) (car relevant))]
        [(? symbol?)
         (define val (hash-ref store e))
         (match val
           [(avalue (== number?) _) #t]
           [(avalue _ _) #f])]))
    (define (guaranteed-all-numbers? es)
      (match es
        ['() #t]
        [`(,head ,tail ...) (and (guaranteed-number? head) (guaranteed-all-numbers? tail))]))
    (match e
      [`(λ ,args ,body) `(λ ,args ,(go body))]
      [(? concrete-value?) e]
      [`(if ,ec ,et ,ef) `(if ,(go ec)
                              ,(go et)
                              ,(go ef))]
      [`(+ ,es ...)
       (if (guaranteed-all-numbers? es)
           `(unsafe+ ,@(map go es))
           `(+ ,@(map go es)))]
      [`(let (,(? symbol? x) ,e) ,body)
       `(let (,x ,(go e)) ,(go body))]
      [`(,ef ,es ...)
       (map go (cons ef es))]
      [(? symbol? x) x]))
  (go exp))



#;(define letadd '(let (a 1) (let (b 2) (+ a b 3))))
#;(match-define (cons letadd-cfg letadd-store) (evaluate letadd))
#;(optimize-plus letadd letadd-cfg letadd-store)

(define (optimize e)
  (match-define (list cfg store kstore) (evaluate e))
  (optimize-plus e cfg store kstore))

(define e evaluate)
(define o optimize)

#;(o '(let (a (if #t 1 3)) (+ (if #f #t 1) (+ a (+ a a) 1 (if #t 1 2)))))

(define (assert v reason)
  (if (not v) (raise reason)
      (void)))

; gets the all continuations related to the given control.
(define (search-for-ks cfg kstore exp)
  (foldl (λ (st accum)
           (match-define `(state ,ctrl ,k) st)
           (if (equal? ctrl exp)
               (cons (hash-ref kstore k) accum)
               accum))
         '() (hash-keys cfg)))

(define (get-ctrls-with-k cfg kstore k)
  (foldl (λ (st accum)
           (match-define `(state ,ctrl ,kaddr) st)
           (define kont (hash-ref kstore kaddr))
           (if (subset? k kont)
               (cons ctrl accum)
               accum))
         '() (hash-keys cfg)))


#;(match-define (list ocfg ostore okstore)
  (e '(let (f (λ (x) (+ x 1))) (+ 2 (f 1)))))
#;(o '(let (f (λ (x) (+ x 1))) (+ 2 (f 1))))

; this shouldnt optimize the body of the let cause vvvvvvv...
(o '(let (f (if #t (λ (x) (+ x 1)) (λ (x) (+ x (if #t 1 #f))))) (+ 2 (f 1))))










