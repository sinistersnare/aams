#lang racket

(provide evaluate)

(require (only-in racket/hash hash-union))

; the file should be able to be swapped out more or less per lattice-type.
; a really shitty and unsafe type-clas system hahaha
(require (only-in "abstract-type-lattice.rkt"
                  join-value bottom
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
   (λ () bottom)))

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
     (define evald (cons ctrl evald-incomplete))
     (list (state (foldl abstract-+ (make-abstract 0) evald) next-kaddr))]
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
  (cons cfg store))

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

#;(e '(let (a 1) (let (b 2) (+ a b 2))))








