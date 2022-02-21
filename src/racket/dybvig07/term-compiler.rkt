#lang racket

;; This code compiles a simple language supporting delimited continuation
;; (via Dybvig et al 07) to a flat database of facts for ingestion into
;; a system like Datalog.
;; It also compiles effect handlers into DCs first, then compiles that.

;; e ::= ae | (newPrompt) | (pushPrompt e e)
;;          | (withSubCont e e) | (pushSubCont e e)
;;          | (call/handler ([x e] ...) e) | (perform e e e)
;;          | (if e e e) | (e e ...)
;;
;; ae ::= (λ (x ...) e) | #t | #f | num | x
;; num = the set of numbers.
;; x = the set of identifiers


;; The global mutable counter
;; So I dont have to pass around a counter...
;; hacky but other option is gensym.
(define cnt 0)
; returns the value of the global cnt then increments it.
(define (++!)
  (define old cnt)
  (set! cnt (add1 cnt))
  old)

(define (compile e)
  (match e
    ;;;; Handling of Atomic Expressions
    [`(λ (,xs ...) ,ebody)
     (define thisid (++!))
     (define argsid (++!))
     (define args (map (λ (x i) `(arglist ,argsid ,x ,i)) xs (range (length xs))))
     (match-define (cons bodyid rest) (compile ebody))
     (cons thisid `((lam ,argsid ,bodyid) ,@args . ,rest))]
    [(? false?)
     (define thisid (++!))
     (cons thisid `((bool ,thisid false)))]
    [(? boolean?)
     (define thisid (++!))
     (cons thisid `((bool ,thisid true)))]
    [(? number?)
     (define thisid (++!))
     (cons thisid `((num ,thisid ,e)))]
    [(? symbol?)
     (define thisid (++!))
     (cons thisid `((identifier ,thisid ,e)))]
    ;;;;; Done handling Atomic Exps.
    [`(newPrompt)
     (define thisid (++!))
     (cons thisid `((newPrompt ,thisid)))]
    [`(pushPrompt ,epr ,eb)
     (define thisid (++!))
     (match-define (cons promptid promptrest) (compile epr))
     (match-define (cons bodyid bodyrest) (compile eb))
     (cons thisid `((pushPrompt ,thisid ,promptid ,bodyid) ,@promptrest . ,bodyrest))]
    [`(withSubCont ,epr ,ef)
     (define thisid (++!))
     (match-define (cons promptid promptrest) (compile epr))
     (match-define (cons fid frest) (compile ef))
     (cons thisid `((withSubCont ,thisid ,promptid ,fid) ,@promptrest . ,frest))]
    [`(pushSubCont ,econt ,ev)
     (define thisid (++!))
     (match-define (cons contid contrest) (compile econt))
     (match-define (cons vid vrest) (compile ev))
     (cons thisid `((pushSubCont ,thisid ,contid ,vid) ,@contrest . ,vrest))]
    [`(if ,ec ,et ,ef)
     (define thisid (++!))
     (match-define (cons cid crest) (compile ec))
     (match-define (cons tid trest) (compile et))
     (match-define (cons fid frest) (compile ef))
     (cons thisid `((if ,thisid ,cid ,tid ,fid) ,@crest ,@trest . ,frest))]
    ; syntax sugar for function application.. Let is lambda!
    [`(let ([,xs ,es] ...) ,ebody)
     (compile `((λ ,xs ,ebody) . ,es))]
    ; syntax sugar for +F+ Reset (AKA pushPrompt)
    [`(call/handler ([,ops ,fs] ...) ,elam)
     (define promptname (gensym 'p))
     (define opbinds (map (λ (op i) `[,op (MakeOp ,i)]) ops (range (length ops))))
     (compile `(let ([,promptname (newPrompt)] . ,opbinds)
                 (pushPrompt ,promptname
                             (,elam (MakeHandler ,promptname . ,fs)))))]
    ; syntax sugar for +F+ Shift (AKA withSubCont),
    ; reifies the continuation, so pushSubCont is sugared too.
    [`(perform ,eop ,eh ,args ...)
     (define kname (gensym 'k))
     (define opname (gensym 'op))
     (define hname (gensym 'h))
     (define kargname (gensym 'karg))
     (define promptvar (gensym 'promptvar))
     (compile `(let ([,opname ,eop] [,hname ,eh])
                 (let ([,promptvar (HandlerPrompt ,hname)])
                   (withSubCont
                    ,promptvar
                    (λ (,kname)
                      (pushPrompt
                       ,promptvar
                       ((HandlerGet ,hname ,opname)
                        (λ (,kargname) (pushPrompt
                                        ,promptvar
                                        (pushSubCont ,kname ,kargname)))
                        . ,args)))))))]
    ; General Function application
    [`(,ef ,es ...)
     (define thisid (++!))
     (define callsitelistid (++!))
     (match-define (cons fnid fnrest) (compile ef))
     ;; TODO: 95% the ordering of the IDs is correct here! Damn fold!
     (match-define (cons callsiteargids callsiteargrests)
                  (foldr (λ (cur acc)
                           (match-define (cons ids rests) acc)
                           (match-define (cons id rest) (compile cur))
                           (cons (cons id ids) (append rest rests)))
                         (cons '() '()) es))
     (define callsitelist
       (map (λ (e i) `(callsitelist ,callsitelistid ,e ,i))
            callsiteargids
            (range (length callsiteargids))))
     (cons thisid `((callsite ,thisid ,fnid ,callsitelistid)
                    ,@fnrest
                    ,@callsitelist
                    . ,callsiteargrests))]))

(define (annotate e)
  (match-define (cons toplevelid toplevelrest) (compile e))
  (cons `(program ,toplevelid) toplevelrest))



;; TODO: if there are no args in a lambda, should we add some sentinel like
;;       `(arglist ,arglistid NONE) so we can check for it?
;;       I think we would need to, or the Datalog will not continue...
;;       SAME WITH THE CALLLSITELIST in function application compilation.
