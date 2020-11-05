#lang racket

(require (only-in racket/hash hash-union))

; a [k=0]-CFA based on the tiny-scheme-cek.rkt
; a CFA is an abstract interpretation, so we take the semantics of
; the tiny-scheme-cek, and we lift it up to the abstract
; this way we can guarantee termination of the interpreter.

; so, whats the difference between the concrete machine in tiny-scheme-cek.rkt
; and the abstract machine here? Well, the abstract machine takes a state,
; and returns a set of states reachable from the given.
; Also, the store is globally available, divorced from the state.
; this reduces algorithmic complexity.

(define (abstraction? exp)
  (match exp
    [`(λ ,_ ,_) #t]
    [else #f]))

(define (concrete-value? v)
  (match v
    [(? boolean?) #t]
    [(? number?) #t]
    [(? abstraction?) #t]
    [(? list?) (andmap concrete-value? v)]
    [else #f]))

(define avt (gensym 'av))
(define (value? exp)
  (match exp
    [`(,(== avt) ,_ ,_) #t]
    [else #f]))

; takes a concrete value and turns it into an abstract value
(define (make-abstract v)
  (match v
    [(? abstraction?) `(,avt BOTTOM ,(set v))]
    [(? concrete-value?) `(,avt ,v ,(set))]
    [else (raise 'bad-value)]))

; shouldnt abstract+ return a list of possibilities?
(define (abstract+ val res)
  (match-define `(,(== avt) ,vv ,vabs) val)
  (match-define `(,(== avt) ,rv ,rabs) res)
  (list
   avt
   (match (cons vv rv)
     [(cons 'BOTTOM _) (raise 'not-given-a-number)]
     [(cons _ 'BOTTOM) (raise 'not-given-a-number)]
     [(cons 'TOP _) 'TOP]
     [(cons _ 'TOP) 'TOP]
     [(cons (? number? vv) (? number? rv)) (+ vv rv)]
     [(cons _ _) (raise 'not-given-a-number)])
   (set-union vabs rabs)))

(define (join-abstr c1 c2) (set-union c1 c2))

(define (join-value v1 v2)
  (match-define `(,(== avt) ,av1 ,c1) v1)
  (match-define `(,(== avt) ,av2 ,c2) v2)
  (define cu (set-union c1 c2))
  (match (cons av1 av2)
    [(cons _ 'BOTTOM) (list avt av1 cu)]
    [(cons 'BOTTOM _) (list avt av2 cu)]
    [else (if (equal? av1 av2) (list avt av1 cu) (list avt av1 cu))]))

(define (state ctrl kaddr) (list 'state ctrl kaddr))
(define (appf evald unevald kaddr) (list 'appf evald unevald kaddr))
(define (addf evald unevald kaddr) (list 'addf evald unevald kaddr))
(define (letf name body kaddr) (list 'letf name body kaddr))
(define (iff et ef kaddr) (list 'iff et ef kaddr))
(define (carf kaddr) (list 'carf kaddr))
(define (cdrf kaddr) (list 'cdrf kaddr))

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
   (λ () (set)))
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
   (λ () `(,avt BOTTOM ,(set)))))

; this steps when the control is an atomic value
; so it needs to check the continuation to see what to do next.
(define (step-value ctrl kont)
  (match kont
    ['TOP '()]
    ['() (raise 'how-the-fuck-did-you-get-bottom)]
    ['mt '()]
    [`(appf ,evald-incomplete () ,next-kaddr)
     (define evald (reverse (cons ctrl evald-incomplete)))
     (match (car evald)
       [`(abstract-value ,_ ,_ ,_ ,abstrs)
        ; (λ (,fnargs ...) ,fnbody)
        (set-map
         abstrs
         (λ (fn) (match fn
                   [`(λ (,fnargs ...) ,fnbody)
                    (define zipped (map cons fnargs (cdr evald)))
                    (for-each update-store zipped)
                    (state fnbody next-kaddr)]
                   [else (raise 'not-given-abstraction-somehow)])))]
       [else (raise 'not-given-abstraction)])]
    [`(appf ,evald-incomplete (,next ,rest ...) ,next-kaddr)
     ;(displayln `(rest: ,rest))
     (define evald (cons ctrl evald-incomplete))
     (define nkaddr (update-kstore ctrl (appf evald rest next-kaddr)))
     (list (state next nkaddr))]
    [`(addf ,evald-incomplete () ,next-kaddr)
     (define evald (cons ctrl evald-incomplete))
     (list (state (foldl abstract+ (make-abstract 0) evald) next-kaddr))]
    [`(addf ,evald-incomplete (,next ,rest ...) ,next-kaddr)
     (define evald (cons ctrl evald-incomplete))
     (define nkaddr (update-kstore ctrl (addf evald rest next-kaddr)))
     (list (state next nkaddr))]
    [`(iff ,et ,ef ,next-kaddr)
     (match ctrl
       [`(abstract-value ,_ #f ,_ ,_)
        (list (state ef next-kaddr))]
       [`(abstract-value ,_ TOP ,_ ,_)
        (list (state et next-kaddr)
              (state ef next-kaddr))]
       [`(abstract-value BOTTOM () () ,(== (set)))
        (raise 'somehow-got-an-uninhabited-value)]
       [else (list (state et next-kaddr))])]
    [`(letf ,name ,body ,next-kaddr)
     (update-store (cons name ctrl))
     (list (state body next-kaddr))]
    [`(carf ,next-kaddr)
     (match ctrl
       [`(abstract-value BOTTOM ,_ ,_ ,_) (raise 'not-given-list)]
       [`(abstract-value TOP ,_ ,_ ,_) (list (state `(abstract-value TOP TOP TOP TOP) next-kaddr))]
       [`(abstract-value ,xs ,_ ,_ ,_) (list (state (car xs) next-kaddr))])]
    [`(cdrf ,next-kaddr)
     (match ctrl
       [`(abstract-value BOTTOM ,_ ,_ ,_) (raise 'not-given-list)]
       [`(abstract-value TOP ,_ ,_ ,_) (list (state `(abstract-value TOP TOP TOP TOP) next-kaddr))]
       [`(abstract-value ,xs ,_ ,_ ,_) (list (state (cdr xs) next-kaddr))])]))

(define (step st)
  (match-define `(state ,ctrl ,kaddr) st)
  ;(displayln `(ctrl: ,ctrl))
  (match ctrl
    [(? value?)
     #; (displayln 'atomic)
     (foldl append '()
            (set-map (hash-ref kstore kaddr)
                     (λ (k) (step-value ctrl k))))]
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
     (define nkaddr (update-kstore ctrl (appf '() es kaddr)))
     (list (state ef nkaddr))]
    [(? symbol?)
     #;(displayln 'sym)
     ; (displayln `(val is: ,(hash-ref store ctrl)))
     (list (state (hash-ref store ctrl) kaddr))
     #;(map (λ (val) (state val kaddr))
            (hash-ref store ctrl))]))

; turns all values in the expression into abstract values.
(define (abstractify e)
  (match e
    [(? concrete-value?) (make-abstract e)]
    [`(+ ,es ...) `(+ ,@(map abstractify es))]
    [`(if ,ec ,et ,ef) `(if ,(abstractify ec) ,(abstractify et) ,(abstractify ef))]
    [`(let (,(? symbol? x) ,e) ,body) `(let (,x ,(abstractify e)) ,(abstractify body))]
    [`(,ef ,es ...) `(,(abstractify ef) ,@(map abstractify es))]
    [(? symbol?) e]))

(define (inject e) (state e 'mt))

(define (evaluate e)
  (set! store (make-hash))
  (set! kstore (make-hash (list (cons 'mt (set 'mt)))))
  ; go takes a list of states to process and a hash of reached states (and where they lead)
  ; and returns a set of reached states, and where they lead (like an edge-list).
  (define (go states reached)
    (define new-reached (make-hash (map (lambda (st) (cons st (step st))) states)))
    (define union-reached (hash-union reached new-reached))
    ; TODO: swap args and use `dropf` instead of filter-not. Feel like itll read better.
    (define todo-states (dropf (append-map identity (hash-values new-reached))
                               (lambda (s) (hash-has-key? union-reached s))))
    (if (empty? todo-states) union-reached (go todo-states union-reached)))
  (go (list (inject (abstractify e))) (hash)))

(define e evaluate)

(define (pgraph cfg)
  (define o (open-output-string))
  (hash-for-each
   cfg
   (λ (k vs)
     (fprintf o "~a ->~n" k)
     (for-each (λ (v) (fprintf o "\t~a~n" v)) vs)))
  (get-output-string o))

#;(e '(let (a (+ 1 2)) (if #f (+ a a) (let (b (+ a a a)) (+ b b)))))
; (e '((λ (u) (u u)) (λ (u) (u u))))
#;store

; infinite loop in a nonterminating machine!
; (e '((λ (u y) (+ y (u u y))) (λ (u y) (+ y (u u y))) 1))

; kstore
#;(e '(let (a 5) (+ a a)))
#;store
; (define paths (e '(let (a 5) (+ a a))))










