#lang racket

; A more fully-featured CEK machine.
; Im gonna turn this into a CFA (tiny-0cfa.rkt) later.
; No store is needed unlike the AAM paper becuase
; the allocation function is just `identity`.

; as a small-step machine, we turn states into new states.
(define (state control env kont)
  (list 'state control env kont))

; a continuation frame saying that the next thing to do
; (after the control computation finishes,
;   which is evaluating the thing in fn position)
; is to evaluate the argument, and then apply the two.
; the env is the environment that is used to
; TODO: would be nice to add multiple arguments.
;      can probably use a list of args, and keep applying
;      until the list is empty? Then make the fn frame?
(define (ar arg env kont)
  (list 'ar arg env kont))

; we have evaluated the argument for the application
; and now we can call the function.
; fn frames are only created when we are fully finished
; evaluating the fn-part of an application
; so now its time to see what the continuation has to say.
; The fn frame stores the fn-part value
; so it can be used when the application happens.
(define (fn val env kont)
  (list 'fn val env kont))

; a frame that represents the computation of an if.
; after the control evaluates, we check to see which branch to
; evaluate (et or ef), and they are evaluated using the given env.
(define (iff et ef env kont)
  (list 'iff et ef env kont))

(define (value? exp)
  (match exp
    [`(λ ,_ ,_) #t]
    [(? number?) #t]
    [(? boolean?) #t]))

;but we will
; turn it abstract soon by not overwriting env-additions
; and then we need to globalize the store also.

; a concrete transition function, from a state to a new state.
; a key difference from other AAMS will be that `v` (from the AAM paper semantics)
; is not the λ-abstractions, but values!
(define (step-concrete curstate)
  (match-define `(state ,ctrl ,env ,kont) curstate)
  (match ctrl
    ; these wont work,
    ; they shouldnt be fixpoints, we should be evaluating
    ; continuations here, right?
    ; see figure 12 of AAM.
    ; yeah, like the abstraction case, we need to check the kont here.
    ; [(? number? n) state]
    ; [(? boolean? b) state]

    ; evaluate the symbol in our environment.
    ; why go back to the oldenv? I think because we are able to use the older one
    ; because we only need the env that created the `v` in the first place.
    [(? symbol? a)
     (match-define (cons v oldenv) (hash-ref env v))
     (state v oldenv kont)]
    [`(if ,econd ,et ,ef)
     (state econd env (iff et ef env kont))]
    ; first evaluate the fn part
    ; and place an ar frame to eval the argument
    ; and then to evaluate the application expression as a whole.
    [`(,ef ,e0)
     ; the ar frame says, after the current computation (hence its a continuation),
     ; evaluate e1, and then after that evaluate the whole application
     ; then do the next continuation.
     (define ar-kont `(ar ,e0 ,env ,kont))
     (state e0 env ar-kont)]
    [(? value? ctrl)
     (match kont
        ; fixpoint! control is atomic, and nothing to do next!
       ['mt curstate]
       ; now we eval the argument and store the current control for later.
       ; we make sure to evaluate the argument in the env that it was found in.
       [`(ar ,e0 ,e0env ,next-kont)
        ; after we evaluate e0, we will jump back to this environment
        ; to do the application, and then do the next kont.
        (state e0 env (fn ctrl env next-kont))]
       ; we have evaluated the argument, now to 'evaluate' the application
       ; we ensure that that the `ef` is an abstraction, and add its
       ; argument to the env, mapped to the arguments value.
       [`(fn (λ ,fnarg ,fnbody) ,appenv ,next-kont)
        ; we store it with the old env because ????????????????????
        ; TODO: ^^^^ the missing piece to my understanding ^^^^
        (define newenv (hash-set appenv fnarg (cons ctrl env)))
        (state fnbody newenv next-kont)]
       [`(fn ,not-abs ,_ ,_)
        (list 'error '("function application requires abstraction at call position given " not-abs))]
       [`(iff ,et ,ef ,oldenv ,next-kont)
        (match ctrl
          [#f (state ef oldenv next-kont)]
          [else (state et oldenv next-kont)])])]))

; forms an initial state from an expression
(define (inject e) (state e (hash) 'mt))

(define (steq? st0 st1)
  (match-define (list 'state c0 e0 k0) st0)
  (match-define (list 'state c1 e1 k1) st1)
  (and (eq? k0 'mt) (eq? k1 'mt) (eq? c0 c1)))

; iterates an initial state until fixpoint
(define (evaluate e)
  (define state0 (inject e))
  (define (run st)
    (match (step-concrete st)
      [(list 'error e) (println `(ERR: ,e)) '()]
      [nextst (if (steq? nextst st)
                  st
                  (run nextst))]))
  (run state0))




















