#lang racket

(require (only-in racket/random random-ref))
(require (only-in racket/hash hash-union))

; An aCESKt* machine!
; implements a k-CFA-like machine. defined by the AAM paper

; This is a k-cfa, so this to the k you want.
; is it really that easy? Seems like `k` is only used in the `tick` function.
; nice!
(define k-value 2)

; make a state of the machine.
(define (state expr env env-store k-store k-addr timestamp)
  (list 'state expr env env-store k-store k-addr timestamp))

; a timestamp is a label and a contour
(define (timestamp label contour)
  (list 'timestamp label contour))

; an address is a (label or variable) and a contour
(define (address label contour)
  (list 'address label contour))


; like `take` in the stdlib, but will return the
; taken items so far if we reach the end of the list.
(define (takesafe lst n)
  (if (or (= n 0) (null? lst))
      '()
      (cons (car lst) (takesafe (cdr lst) (- n 1)))))

(define (tick st kont)
  (match st
    [(list 'state (cons (? symbol? _) _) _ _ _ _ t) t]
    [(list 'state (cons `(,e0 ,e1) elabel) _ _ _ _ (list 'timestamp tlabel contour))
     (timestamp elabel contour)]
    [(list 'state (cons `(λ ,xvar ,ebody) elabel) _ _ _ _ (list 'timestamp label contour))
     (match kont
       ; HELP: intereting that timestamp doesnt change here. Why?
       ; need to understand this whole thing a bit better.
       [(list 'ar _ _ _) (timestamp label contour)]
       ; add the label to the contour list, and then take the floor of it.
       ; the empty list (bullet/nil from AAM) is only allowed in label position,
       ; not contour position. Could cause issues!
       [(list 'fn _ _ _) (timestamp '() (takesafe (cons label contour) k-value))]
       [else (raise `(bad-kont-tick st: ,st kont: ,kont))])]
    [else (raise `(bad-tick-args st: ,st kont: ,kont))]))

(define (alloc st kont)
  (match st
    [(list 'state (cons `(,(cons e0 e0label) ,e1) _) _ _ _ _ (list 'timestamp _ contour))
     (address e0label contour)]
    [(list 'state (cons `(λ ,_ ,_) _) _ _ k-store k-addr (list 'timestamp _ contour))
     (match kont
       ; HELP: What goes here?
       ['mt (address 'mt contour)]
       [`(ar ,(cons _ elabel) ,_ ,_) (address elabel contour)]
       [`(fn (λ ,x ,_) ,_ ,_) (address x contour)]
       [else (raise `(bad-kont-alloc st: ,st kont: ,kont))])]
    [else (raise `(bad-alloc-args st: ,st kont: ,kont))]))

; create an initial state around a closed expression
(define (inj-aceskt* e)
  (define a0 (address '0 '()))
  (define t0 (timestamp '() '()))
  ; expr , env , env-store , k-store , k
  ; where the stores are Addr -> P(ValueType). 
  (state e (hash) (hash) (hash a0 (set 'mt)) a0 t0))

; move the machine 1 step from a given state.
; takes a single state, returns a list of states that can be reached.
(define (step-aceskt* st)
  (match-define (list 'state expr env env-store k-store k-addr timestamp) st)
  (match expr
    [(cons (? symbol? x) label)
     ; current-xs is all (v pprime) pairs at the address `x`.
     ; current-ks is all continuations at the address `k-addr`
     ; we need to return new states based on each combo of those two.
     (define current-xs (set->list (hash-ref env-store (hash-ref env x))))
     (define current-ks (set->list (hash-ref k-store k-addr)))
     (define products (cartesian-product current-xs current-ks))
     (map (lambda (product)
            (match-define `(,(cons val storeprime) ,k) product)
            (state val storeprime env-store k-store k (tick st k)))
          products)]
    [(cons `(,e0 ,e1) label)
     ; current-ks is all continuations at the current continuation address.
     (define current-ks (hash-ref k-store k-addr))
     (set-map current-ks
              (lambda (current-k)
                (define b-addr (alloc st current-k))
                (define new-cont `(ar ,e1 ,env ,k-addr))
                (state e0 env env-store (hash-update k-store b-addr
                                                     (lambda (k-set) (set-add k-set new-cont))
                                                     (lambda () (set new-cont)))
                       b-addr (tick st current-k))))]
    [(cons `(λ ,xarg ,ebody) label)
     (define current-ks (hash-ref k-store k-addr))
     (set-map
      current-ks
      (lambda (current-k)
        (define b-addr (alloc st current-k))
        (match current-k
          ; at a fixpoint, return state
          ['mt st]
          [`(ar ,e ,pprime ,c)
           (define new-cont `(fn (λ ,xarg ,ebody) ,env ,c))
           (state e pprime env-store (hash-update k-store b-addr
                                                  (lambda (k-set) (set-add k-set new-cont))
                                                  (lambda () (set new-cont)))
                  b-addr (tick st current-k))]
          [`(fn (λ ,x ,e) ,pprime ,c)
           (define env-item (cons `(λ ,xarg ,ebody) env))
           (state e (hash-set pprime x b-addr)
                  (hash-update env-store b-addr
                               (lambda (env-set) (set-add env-set env-item))
                               (lambda () (set env-item)))
                  k-store c (tick st current-k))]
          [else (raise `(bad-cont: ,current-k))])))]
    [else (raise (list 'bad-syntax expr env env-store k-store k-addr))]))

; evaluate from an initial state
; this works differently from non-abstract abstract-machines, because here
; a step will return a list of states. We need to reach a fix-point
; which is when we have already seen all the states reached.
; HELP: But isnt the defn of fixpoint `x where f(x) = x`?
; how is 'reached before already' a fixpoint? Am I visualizing the step function wrong?
(define (evaluate e)
  ; add labels to `e`.
  (define (label e)
    (match e
      [(? symbol? x) (cons x (gensym 'lab))]
      [`(,e0 ,e1) (cons `(,(label e0) ,(label e1)) (gensym 'lab))]
      [`(λ ,x ,e) (cons `(λ ,x ,(label e)) (gensym 'lab))]
      [else `(labeling-error ,e)]))
  ; go takes a list of states to process and a hash of reached states (and where they lead)
  ; and returns a set of reached states, and where they lead (like an edge-list).
  (define (go states reached)
    ; compute new reached => new-reached
    ; from the newly reached states, figure which ones we havent seen before. => todo-states
    ; add all reached into total reached => union-reached
    ; If todo-states is empty: we are at fixed point, return union-reached. Else:
    ; Run `go` with todo-states and union-reached
    (define new-reached (make-hash (map (lambda (st) (cons st (step-aceskt* st))) states)))
    ; shoudnt be hit by dupe errors, as we check when calculating todo-states for possible dupes.
    (define union-reached (hash-union reached new-reached))
    ; use union-reached instead of reached because when we reach a fixpoint we need to catch it.
    ; TODO: swap args and use `dropf` instead of filter-not. Feel like itll read better.
    (define todo-states (dropf (append-map identity (hash-values new-reached))
                               (lambda (s) (hash-has-key? union-reached s))))
    (if (empty? todo-states) union-reached (go todo-states union-reached)))
  (go (list (inj-aceskt* (label e))) (hash)))

(define edges (evaluate '((λ n (λ s (λ z (s ((n s) z))))) (λ s (λ z z)))))

#;(println "digraph G {")
#;(hash-for-each
 edges
 (lambda (src dests)
   (for-each (lambda (dest) (println (string-append src " -> " dest))) dests)))
#;(println "}")