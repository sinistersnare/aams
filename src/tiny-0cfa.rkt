#lang racket

(require (only-in racket/hash hash-union))

; a [k=0]-CFA based on the tiny-scheme-cek.rkt
; a CFA is an abstract interpretation, so we take the semantics of
; the tiny-scheme-cek, and we lift it up to the abstract
; this way we can guarantee termination (??? CAN WE? or just decidability?)

; so, whats the difference between the concrete machine in tiny-scheme-cek.rkt
; and the abstract machine here? Well, the abstract machine takes a state,
; and returns a set of states reachable from the given.

; use a global store for all steps of an evaluation
; When we call `evaluate` the store is reset.
; this is a mapping from a symbol to a set of values.
; All are possible inhabitants of the symbol.
; TODO: change it to a cooler thing than a powerset lattice!
(define store (make-hash))

(define (value? exp)
  (match exp
    [`(λ ,_ ,_) #t]
    [(? number?) #t]
    [(? boolean?) #t]
    [else #f]))

(define (state ctrl kont) (list 'state ctrl kont))
(define (appf evald unevald kont) (list 'appf evald unevald kont))
(define (addf evald unevald kont) (list 'addf evald unevald kont))
(define (letf name body kont) (list 'letf name body kont))
(define (iff et ef kont) (list 'iff et ef kont))

; the value should be a hash-set cause rn it can copy the same value.
(define (update bnd)
  (match-define (cons name val) bnd)
  (hash-update! store name
                (λ (vals) (cons val vals))
                (lambda () '())))

(define (step st)
  (match-define `(state ,ctrl ,kont) st)
  #;(displayln `(ctrl: ,ctrl ,(value? ctrl)))
  (match ctrl
    [(? value?)
     #;(displayln 'atomic)
     (match kont
       ['mt '()]
       [`(appf ,evald-incomplete () ,next-kont)
        (define evald (reverse (cons ctrl evald-incomplete)))
        (match (car evald)
          [`(λ (,fnargs ...) ,fnbody)
           (define zipped (map cons fnargs (cdr evald)))
           (for-each update zipped)
           (list (state fnbody next-kont))]
          [else (raise 'not-given-abstraction)])]
       [`(appf ,evald-incomplete (,next ,rest ...) ,next-kont)
        (define evald (cons ctrl evald-incomplete))
        (list (state next (appf evald rest next-kont)))]
       [`(addf ,evald-incomplete () ,next-kont)
        (define evald (cons ctrl evald-incomplete))
        (list (state (foldl + 0 evald) next-kont))]
       [`(addf ,evald-incomplete (,next ,rest ...) ,next-kont)
        (define evald (cons ctrl evald-incomplete))
        (list (state next (addf evald rest next-kont)))]
       [`(iff ,et ,ef ,next-kont)
        (match ctrl
          [#f (list (state ef next-kont))]
          [else (list (state et next-kont))])]
       [`(letf ,name ,body ,next-kont)
        (update (cons name ctrl))
        (list (state body next-kont))])]
    [`(+ ,es ...)
     #;(displayln 'add)
     (list (state 0 (addf '() es kont)))]
    [`(if ,econd ,et ,ef)
     #;(displayln 'if)
     (list (state econd (iff et ef kont)))]
    [`(let (,name ,exp) ,body)
     #;(displayln 'let)
     (list (state exp (letf name body kont)))]
    [`(,ef ,es ...)
     #;(displayln `(appl ,ef and ,es))
     (list (state ef (appf '() es kont)))]
    [(? symbol?)
     #;(displayln 'sym)
     (map (λ (val) (state val kont))
          (hash-ref store ctrl))]))


(define (inject e) (state e 'mt))

(define (evaluate e)
  ; go takes a list of states to process and a hash of reached states (and where they lead)
  ; and returns a set of reached states, and where they lead (like an edge-list).
  (define (go states reached)
    (define new-reached (make-hash (map (lambda (st) (cons st (step st))) states)))
    (define union-reached (hash-union reached new-reached))
    ; TODO: swap args and use `dropf` instead of filter-not. Feel like itll read better.
    (define todo-states (dropf (append-map identity (hash-values new-reached))
                               (lambda (s) (hash-has-key? union-reached s))))
    (if (empty? todo-states) union-reached (go todo-states union-reached)))
  (go (list (inject e)) (hash)))

(define e evaluate)

#;(e '(let (a (+ 1 2)) (if #f (+ a a) (let (b (+ a a a)) (+ b b)))))
#;(e '((λ (u) (u u)) (λ (u) (u u))))
#;store
















