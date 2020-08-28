#lang racket

; A state consists of
;     x ∈ Varx  -- The set of identifiers
;     v ∈ Val ::= (λx.e)
;     e ∈ Exp ::=  x | (e e) | (λx.e)
;     ρ ∈ Env = Var → (Val x Env)
;     κ ∈ Kont ::= mt | ar(e,ρ,κ) | fn(v,ρ,κ)
;     ς ∈ Σ = Exp x Env x Kont
; (from AAM paper)

; the initial state of the CEK machine, given a closed-expression.
(define (inj-cek e) (list e (hash) 'mt))

; The function makes one step in the machine. Defined by `figure 1` of the AAM paper.
; exp  ∈ Exp
; env  ∈ Env
; cont ∈ Kont
; it returns a modified exp, env, cont, which can be passed back into
; the step function to run another step.
(define (cek-step exp env cont)
  (match exp
    ; if the control string is simply a symbol, then we check it in the hash, and return that.
    [(? symbol? x)
     (match-define `(,v ,pprime) (hash-ref env x (raise `(no var ,x found in env ,env))))
     (list v pprime cont)]
    
    [`(,e0 ,e1)
     (list e0 env `(ar ,e1 ,env ,cont))]
    [`(λ ,(? symbol? x) ,e)
     (match cont
       ; this is the final state of a machine, there is nothing to evaluate here.
       ; we need to check for this state (lambda with mt cont) after calling step
       ; to see that we are at the end.
       ['mt (list exp env cont)]
       [`(ar ,e ,pprime ,k)
        (list e pprime `(fn ,exp ,pprime ,k))]
       [`(fn (λ ,x ,e) ,pprime ,k)
        (list e (hash-set pprime x (list exp env)) k)]
       [else (raise `(WAT! ,exp ,env ,cont))])]
    [else (raise `(BAD-SYNTAX! ,exp ,env ,cont))]))

; do a single step from an initial state with e.
(define (s e) (apply cek-step (inj-cek e)))

; evaluates e from an initial state until it reaches a fixed-point: <v, p, mt>.
(define (evaluate e)
  (define (is-fixed st)
    (match st
      [`((λ ,x ,e) ,env mt) #t]
      [else #f]))
  (define (go st)
    (define next-st (apply cek-step st))
    (if (is-fixed next-st) next-st (go next-st)))
  (go (inj-cek e)))

; lazy davis shortcut
(define (e exp) (evaluate exp))

; (evaluate '((λ n (λ s (λ z (s ((n s) z))))) (λ s (λ z z))))
; => '((λ s (λ z (s ((n s) z)))) #hash((n . ((λ s (λ z z)) #hash()))) mt)
; So n is still here at the end, but its in the env. Is this the correct output of this machine?
; I think so!








