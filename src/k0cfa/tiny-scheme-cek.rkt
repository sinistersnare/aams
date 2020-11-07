#lang racket

(require (only-in racket/hash
                  hash-union))
(require (only-in "abstract-type-lattice.rkt"
                  avalue avalue?))
(require (only-in "tiny-0cfa.rkt"
                  optimize))

(define ERROR-SIGIL (gensym 'err))

; A more fully-featured CEK machine.
; Im gonna turn this into a CFA (tiny-0cfa.rkt) later.
; No store is needed unlike the AAM paper becuase
; the allocation function is just `identity`.
; so the CFA will need to be a CESK* so continuations dont get loopy
; in a program like
#; (e '((λ (u y) (+ y (u u y))) (λ (u y) (+ y (u u y))) 1))
; where the continuation always grows so we never hit a fixpoint.

; we will turn it abstract soon by not overwriting env-additions
; and then we need to globalize the env also.


; as a small-step machine, we turn states into new states.
(define (state control env kont)
  (list 'state control env kont))

; An application continuation frame
; this combines the ar and fn frames of the AAM paper
; to allow a multi-argument application
; and therefore a multi-argument abstraction.
; it contains the environment that evaluates each argument (including the fn part)
; and the continuation for what to do after the application finishes.
; the arguments are in two positions, `evald` and `unevald`
; the when the unevald is empty, we do the application.
(define (appl evald unevald appenv kont)
  (list 'appl evald unevald appenv kont))


; a frame that represents the computation of an if.
; after the control evaluates, we check to see which branch to
; evaluate (et or ef), and they are evaluated using the given env.
(define (iff et ef env kont)
  (list 'iff et ef env kont))

; very similar to the appl frame
; but after evaluating arguments they are added together
(define (addk evald unevald env kont)
  (list 'addk evald unevald env kont))

(define (letk name body env kont)
  (list 'letk name body env kont))

(define (unsafe-addk evald unevald env kont)
  (list 'unsafe-addk evald unevald env kont))

(define (value? exp)
  (match exp
    [`(λ ,_ ,_) #t]
    [(? number?) #t]
    [(? boolean?) #t]
    [else #f]))

; takes 2 lists and zips them together
; (ezip '(a b) (1 2)) => ((a . 1) (b . 2))
; if they are differently sized, then return the ERROR-SIGIL
(define (ezip xs1 xs2)
  (with-handlers ([exn:fail? (λ (e) ERROR-SIGIL)])
    (map cons xs1 xs2)))

; a concrete transition function, from a state to a new state.
; a key difference from other AAMS will be that `v` (from the AAM paper semantics)
; is not the λ-abstractions, but values!
(define (step-concrete curstate)
  (match-define `(state ,ctrl ,env ,kont) curstate)
  (match ctrl
    ; had to put this first to stop the catchall 'symbol' match from
    ; thinking λ is a symbol.
    [(? value? ctrl)
     (match kont
       ; fixpoint! control is atomic, and nothing to do next!
       ['mt curstate]
       ; here, we have finished evaluating all of the expressions
       ; in an application form. So we now evaluate the application
       [`(appl ,evald () ,applenv ,next-kont)
        (define all-evald (cons ctrl evald))
        (match-define `(,fn ,args ...) (reverse all-evald))
        (match fn
          [`(λ (,fnbindings ...) ,fnbody)
           (define zipped (ezip fnbindings args))
           (if (eq? zipped ERROR-SIGIL)
               (list 'error `(Args mismatched: Require ,(length fnbindings) but given ,(length args)))
               (let* ([argbindings
                       ; binding looks like (cons k v) and we want (cons k (cons v env))
                       ; HELP: Idk why env is added to the env here... THINK DAVIS!
                       ;     I think its a newer environment, so why would that matter... THINK!
                       (map (λ (binding) (cons (car binding) (cons (cdr binding) env))) zipped)]
                      [newenv
                       ; replace old values with new ones on conflict.
                       (hash-union applenv (make-hash argbindings)
                                   #:combine/key (λ (k v1 v2) v2))])
                 ; we need to map the arguments to the evald expressions.
                 (state fnbody newenv next-kont)))]
          [not-abs (list 'error `(application requires abstraction at call position given
                                              ,not-abs))])]
       [`(appl ,evald (,nextarg ,rest ...) ,applenv ,next-kont)
        ; the args are added in reverse order, so we need to reverse when we finally apply.
        (define appl-kont (appl (cons ctrl evald) rest applenv next-kont))
        (state nextarg applenv appl-kont)]
       ; now we eval the argument and store the current control for later.
       ; we make sure to evaluate the argument in the env that it was found in.
       [`(iff ,et ,ef ,oldenv ,next-kont)
        (match ctrl
          [#f (state ef oldenv next-kont)]
          [else (state et oldenv next-kont)])]
       ; now do the addition, as no args are left.
       [`(addk ,evald () ,oldenv ,next-kont)
        (define args (cons ctrl evald)) ; args should be values!
        (define addition
          (foldl (λ (v res) (if (eq? res ERROR-SIGIL) ERROR-SIGIL
                                (if (number? v) (+ v res) ERROR-SIGIL))) 0 args))
        (if (eq? addition ERROR-SIGIL)
            (list 'error `(not given only numbers in +))
            (state addition env next-kont))]
       ; have some args left to evaluate.
       [`(addk ,evald (,arg ,rest ...) ,oldenv ,next-kont)
        (define new-evald (cons ctrl evald))
        (define new-addk (addk new-evald rest oldenv next-kont))
        ; make sure to evaluate the arg with the env it was made in.
        (state arg oldenv new-addk)]
       [`(unsafe-addk ,evald () ,oldenv ,next-kont)
        ; we dont need to do type checking cause its UNSAFE!
        ; (AKA its not our job to verify the args of the addition here)
        (state (apply + (cons ctrl evald)) next-kont)]
       [`(unsafe-addk ,evald (,arg ,rest ...) ,oldenv ,next-kont)
        (define new-evald (cons ctrl evald))
        (define new-addk (unsafe-addk new-evald rest oldenv next-kont))
        ; make sure to evaluate the arg with the env it was made in.
        (state arg oldenv new-addk)]
       [`(letk ,name ,body ,old-env ,next-kont)
        (if (symbol? name)
            ; HELP: is this the correct env?
            (let ([new-env (hash-set old-env name (cons ctrl env))])
              (state body new-env next-kont))
            (list 'error `(binding ,name must be a symbol)))])]
    ; a simple conditional.
    ; the only way to take the false branch is if `econd` evaluates to `#f`.
    [`(if ,econd ,et ,ef)
     (state econd env (iff et ef env kont))]
    ; addition! Useful for obvious reasons, its something to do!
    [`(+ ,args ...)
     (define add-kont (addk '() args env kont))
     ; for consistency just evaluate the identity first.
     ; this way we dont need to split the args and `(+)` works.
     (state 0 env add-kont)]
    [`(let (,name ,exp) ,body)
     (define let-kont (letk name body env kont))
     (state exp env let-kont)]
    ; first evaluate the fn part
    ; and place an ar frame to eval the argument
    ; and then to evaluate the application expression as a whole.
    [`(,ef ,es ...)
     ; we are in an application, so we use an application frame
     ; which says to evaluate all its arguments, then do an application, then do the next kont.
     (define appl-kont (appl '() es env kont))
     (state ef env appl-kont)]
    ; evaluate the symbol in our environment.
    ; why go back to the oldenv? I think because we are able to use the older one
    ; because we only need the env that created the `v` in the first place.
    [(? symbol? a)
     (define binding (hash-ref env a ERROR-SIGIL))
     (if (eq? binding ERROR-SIGIL)
         (list 'error `(variable ,a not found in environment ,env))
         (state (car binding) (cdr binding) kont))]))

; forms an initial state from an expression
(define (inject e) (state e (hash) 'mt))

(define (steq? st0 st1)
  (match-define (list 'state c0 e0 k0) st0)
  (match-define (list 'state c1 e1 k1) st1)
  (and (eq? k0 'mt) (eq? k1 'mt) (eq? c0 c1)))

; iterates an initial state until fixpoint
(define (evaluate e)
  (define optimized-prog (optimize e))
  (define state0 (inject optimized-prog))
  (define (run st)
    (match (step-concrete st)
      [(list 'error err) `(ERR: ,err)]
      [nextst (if (steq? nextst st)
                  st
                  (run nextst))]))
  (run state0))

(define e evaluate)




