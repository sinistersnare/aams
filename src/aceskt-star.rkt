#lang racket

(require (only-in racket/hash hash-union))

; An aCESKt* machine!
; implements a k-CFA-like machine. defined by the AAM paper

; This is a k-cfa, so this to the k you want.
; is it really that easy? Seems like `k` is only used in the `tick` function.
; nice!
(define k-value 0)

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
    [(list 'state (cons #f _) _ _ _ _ t) t]
    [(list 'state (cons `(,e0 ,e1) elabel) _ _ _ _ (list 'timestamp _ contour))
     (timestamp elabel contour)]
    ; HELP: Idk what to do here, cause i dont truly understand
    ; the way these work.
    [(list 'state (cons `(if ,e0 ,e1, e2) iflabel) _ _ _ _ (list 'timestamp _ contour))
     (timestamp iflabel contour)]
    [(list 'state (cons `(λ ,xvar ,ebody) elabel) _ _ _ _ (list 'timestamp label contour))
     (match kont
       ; HELP: intereting that timestamp doesnt change here. Why?
       ; need to understand this whole thing a bit better.
       [(list 'ar _ _ _) (timestamp label contour)]
       ; add the label to the contour list, and then take the floor of it.
       ; the empty list (bullet/nil from AAM) is only allowed in label position,
       ; not contour position. Could cause issues!
       [(list 'fn _ _ _) (timestamp '() (takesafe (cons label contour) k-value))]
       [else (raise `(bad-kont-tick kont: ,kont st: ,st))])]
    [else (raise `(bad-tick-args st: ,st kont: ,kont))]))

(define (alloc st kont)
  (match st
    [(list 'state (cons `(,(cons e0 e0label) ,e1) _) _ _ _ _ (list 'timestamp _ contour))
     (address e0label contour)]
    [(list 'state (cons `(if ,e0 ,e1, e2) iflabel) _ _ _ _ (list 'timestamp _ contour))
     (address iflabel contour)]
    [(list 'state (cons #f flabel) _ _ _ _ (list 'timestamp _ contour))
     (address flabel contour)]
    [(list 'state (cons `(λ ,_ ,_) _) _ _ k-store k-addr (list 'timestamp _ contour))
     (match kont
       ['mt (address 'mt contour)]
       [`(ar ,(cons _ elabel) ,_ ,_) (address elabel contour)]
       [`(fn ,(cons `(λ ,x ,_) (? symbol?)) ,_ ,_) (address x contour)]
       [else (println kont) (raise `(bad-kont-alloc kont: ,kont st: ,st))])]
    [else (println st) (raise `(bad-alloc-args st: ,st kont: ,kont))]))

; create an initial state around a closed expression
(define (inj-aceskt* e)
  (define a0 (address '0 '()))
  (define t0 (timestamp '() '()))
  ; expr , env , env-store , k-store , k
  ; where the stores are Addr -> P(ValueType). 
  (state e (hash) (hash) (hash a0 (set 'mt)) a0 t0))

; The store is a mappingof AddrType -> P(ValType)
; if the address is not in the mapping, its added as a singleton set
; if the address is in the mapping, then the val is added to the set
(define (create-or-add store addr val)
  (hash-update store addr
               (lambda (value-set) (set-add value-set val))
               (lambda () (set val))))

; Move the machine 1 step.
; As this is an abstract machine, 1 given states returns a list of new states.
(define (step-aceskt* st)
  (match-define (list 'state (cons expr (? symbol? label)) env env-store k-store k-addr _) st)
  (define current-ks (hash-ref k-store k-addr))
  ; the lambda returns a list of states
  ; so the set-map returns a list of list of states.
  ; we flatten it so its only a single list.
  (foldl
   append
   '()
   (set-map
    current-ks
    (lambda (k)
      (define u (tick st k))
      (match expr
        [(? symbol? x)
         (println 'sym)
         (define vals-at-x (hash-ref env-store (hash-ref env x)))
         (set-map vals-at-x (lambda (vals)
                              (match-define (cons val envprime) vals)
                              (state val envprime env-store k-store k-addr (tick st k))))]
        [`(,e0 ,e1)
         (println 'app)
         (define b (alloc st k))
         (list (state e0 env env-store (create-or-add k-store b `(ar ,e1 ,env ,k-addr)) b u))]
        [`(if ,e0 ,e1 ,e2)
         (println 'if)
         (define b (alloc st k))
         (define new-k `(if ,e1 ,e2 ,env ,k-addr))
         (define new-k-store (create-or-add k-store b new-k))
         (list (state e0 env env-store new-k-store b u))]
        [v
         (match k
           [`(ar ,e ,pprime ,c)
            (println 'ark)
            (define b (alloc st k))
            (define new-cont `(fn ,(cons v label) ,env ,c))
            (list (state e pprime env-store (create-or-add k-store b new-cont) b u))]
           [`(fn ,(cons `(λ ,x ,e) fnlabel) ,pprime ,c)
            (println 'fnk)
            (define b (alloc st k))
            (list (state e (hash-set pprime x b)
                         (create-or-add env-store b (cons (cons v fnlabel) env)) k-store c u))]
           [`(if ,e0 ,e1 ,pprime ,c)
            (println 'ifkont)
            (list (state (if (equal? v #f) e1 e0) pprime env-store k-store c u))]
           [else (raise `(bad-match ,st))])])))))

; evaluate from an initial state
; this works differently from non-abstract abstract-machines, because here
; a step will return a list of states. We need to reach a fix-point
; which is when we have already seen all the states reached.
; HELP: But isnt the defn of fixpoint `x where f(x) = x`?
; how is 'reached before already' a fixpoint? Am I visualizing the step function wrong?
(define (evaluate e)
  ; add labels to `e`.
  (define (label e)
    (define lab (gensym 'lab))
    (match e
      ['#f (cons '#f lab)]
      ; TODO: numbers!
      ;[`,(? number? n) (cons n lab)]
      [`(if ,e0 ,e1 ,e2) (cons `(if ,(label e0) ,(label e1) ,(label e2)) lab)]
      [(? symbol? x) (cons x lab)]
      [`(,e0 ,e1) (cons `(,(label e0) ,(label e1)) lab)]
      [`(λ ,x ,e) (cons `(λ ,x ,(label e)) lab)]
      [else (raise `(labeling-error ,e))]))
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

;(define edges (evaluate '((λ n (λ s (λ z (s ((n s) z))))) (λ s (λ z z)))))
(define edges (evaluate '((λ x (x x)) (λ x (x x)))))
; (step-aceskt* (state '(λ x (((x . lab1) (x . lab2)) . lab3)) '() '() '() '() '()))
; (step-aceskt* (state '(λ x (((x . lab99679) (x . lab99680)) . lab99681)) '() '() '() '() '()))
(evaluate '((λ x x) (if #f (λ x (x x)) (λ x x))))

; use the formatting module!
#;(println "digraph G {")
#;(hash-for-each
   edges
   (lambda (src dests)
     (for-each (lambda (dest) (println (string-append src " -> " dest))) dests)))
#;(println "}")


; found some λ-examples with this syntax, so ez transformation to mine.
(define (unwrap e)
  (match e
    [(? symbol? x) x]
    [`(,efn ,earg) `(,(unwrap efn) ,(unwrap earg))]
    [`(λ (,(? symbol? fnarg)) ,e) `(λ ,fnarg ,(unwrap e))]))
(define (eu e) (evaluate (unwrap e)))


