#lang racket



(define abort '())
(define mk '())

;; some functions for creating and manipulating the meta-continuation structure.
; mk constructor: creates an empty continuation
(define (emptys) '())
; mk constructor: push prompt to meta-continuation
(define (pushp p mk) '())
; mk constructor: push continuation segment to meta-continuation
(define (pushseg k mk) '())
; splits the meta continuation at a prompt
(define (splitseq p mk) (values '() '()))
; combines two meta-continuation sequences. (++)
(define (appendseq s1 s2) '())

; makes a new prompt. I think in a realisitc
; system this should be combined with 'push-prompt'
; at the very least, there should be a utility function
; that combines new-prompt and push-prompt.
(define (new-prompt) (symbol->string (gensym 'prompt)))

; the equivalent to 'reset'
(define (push-prompt p th)
  (call/cc (lambda (k)
             (set! mk (pushp p (pushseg k mk)))
             (abort th))))

; the equivalent to 'shift'
(define (with-sub-kont p f)
  (let-values ([(subk mk*) (splitseq p mk)])
    (set! mk mk*)
    (call/cc (lambda (k)
               (abort (lambda () (f (pushseg k subk))))))))

; in a 'real' impl in a AM or a compiler, I think
; that continuations should just be used as functions
; leaving this unneeded.
(define (push-sub-kont subk th)
  (call/cc (lambda (k)
             (set! mk (appendseq subk (pushseg k mk)))
             (abort th))))

(define (run-cc th)
  (set! mk (emptys))
  (underflow ((call/cc (lambda (k)
                         (set! abort k)
                         (abort th))))))

(define (underflow v)
  (match mk
    ['() v]
    [`(pushp ,_ ,mk*)
     (set! mk mk*)
     (underflow v)]
    [`(pushseg ,k ,mk*)
     (set! mk mk*)
     (k v)]))

; Gunter et al. 1995 - cupto. (basically just withSubKont)
(define f--
  (lambda (p f)
    (with-sub-kont p (lambda (k) (f (reify k))))))

; Hieb & Dybvig 1990 - spawn.
(define f-+
  (lambda (p f)
    (with-sub-kont p (lambda (k) (f (reifyP p k))))))

; Felleisen et al. 1987 original F operator.
; from A syntactic theory of sequential control
(define f+-
  (lambda (p f)
    (with-sub-kont p (lambda (k) (push-prompt p (thunk (f (reify k))))))))

; Danvy shift
(define f++
  (lambda (p f)
    (with-sub-kont p (lambda (k) (push-prompt p (thunk (f (reifyP p k))))))))

(define (reify k v) (push-sub-kont k (thunk v)))
(define (reifyP p k v) (push-prompt p (thunk (push-sub-kont k (thunk v)))))
