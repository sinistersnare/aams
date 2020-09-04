#lang racket

(require (only-in racket/random random-ref))
(require (only-in racket/hash hash-union))

; An aCESKt* with no timestamp, so its monotonic.
; A 0CFA.
; so i guess its just a aCESK* machine. but its too late to change the file name now!

; make a state of the machine.
(define (make-state expr env env-store k-store cont-addr)
  (list expr env env-store k-store cont-addr))

; create an initial state around a closed expression
(define (inj-aceskt* e)
  ; expr , env , env-store , k-store , k
  ; where the stores are Addr -> P(ValueType). 
  (make-state e (hash) (hash) (hash 0 (set 'mt)) 0))

; move the machine 1 step from a given state.
; takes a single state, returns a list of states that can be reached.
(define (step-aceskt* state)
  (println `(stepping: ,state))
  (match-define (list expr env env-store k-store cont-addr) state)
  (match expr
    [(? symbol? x)
     ; i think if we add first-class continuations (so then continuations could be in the env-store)
     ; then the 2-store method would become annoying, and we would just go back to structure checking
     ; structure checking as in, we need access to the continuation,
     ; it could be any variable (becauase we are storing them alongside eachother in sets)
     ; so the solution would be ensure that the `k` is a continuation, or just use 2 stores.
     (define res-set (hash-ref env-store (hash-ref env x)))
     ; anyways, res-set is a set of (v pprime) lists.
     ; we need to return new states based on each element of res-set.
     (set-map res-set (lambda (res) (make-state (car res) (cdr res) env-store k-store cont-addr)))]
    [`(,e0 ,e1)
     ; current-ks is all continuations at the current continuation address.
     (define current-ks (hash-ref k-store cont-addr))
     ; HELP: So alloc is `alloc(varsigma, k) where k is all current-ks
     ; but im not sure what to do with `k` in the alloc func,
     ; update:
     ; im just gonna use the k itself as the alloc-address!!
     ; it seems like itll work! But I have no idea what working is!
     ; so the mt entry is 0 -> mt. Then the next one would be
     ; mt -> ar(e1 env cont-addr)... thats weird.
     (set-map current-ks
              (lambda (k-addr)
                (define new-cont `(ar ,e1 ,env ,cont-addr))
                (make-state e0 env env-store (hash-update k-store k-addr
                                                          (lambda (k-set) (set-add k-set new-cont))
                                                          (lambda () (set new-cont)))
                            k-addr)))]
    [`(λ ,xarg ,ebody)
     (define current-ks (hash-ref k-store cont-addr))
     (set-map
      current-ks
      (lambda (k-addr)
        (match k-addr
          ; at a fixpoint, return state
          ['mt state]
          [`(ar ,e ,pprime ,c)
           (define new-cont `(fn ,expr ,env ,c))
           (make-state e pprime env-store (hash-update k-store k-addr
                                                       (lambda (k-set) (set-add k-set new-cont))
                                                       (lambda () (set new-cont)))
                       k-addr)]
          [`(fn (λ ,x ,e) ,pprime ,c)
           (define env-item (cons expr env))
           (make-state e (hash-set pprime x k-addr)
                       (hash-update env-store k-addr
                                    (lambda (env-set) (set-add env-set env-item))
                                    (lambda () (set env-item)))
                       k-store c)]
          [else (raise `(bad-cont: ,k-addr))])))]
    [else (raise (list 'bad-syntax expr env env-store k-store cont-addr))]))

; evaluate from an initial state
; this works differently from non-abstract abstract-machines, because here
; a step will return a list of states. We need to reach a fix-point
; which is when we have already seen all the states reached.
; HELP: But isnt the defn of fixpoint `x where f(x) = x`?
; how is 'reached before already' a fixpoint? Am I visualizing the step function wrong?
(define (evaluate e)
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
    (define todo-states (filter-not (lambda (s) (hash-has-key? union-reached s))
                                    (append-map identity (hash-values new-reached))))
    (if (empty? todo-states) union-reached (go todo-states union-reached)))
  (go (list (inj-aceskt* e)) (hash)))

(define edges (evaluate '((λ n (λ s (λ z (s ((n s) z))))) (λ s (λ z z)))))

