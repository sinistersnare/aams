#lang racket

(provide abstraction? concrete-value?
         state appf addf letf iff carf cdrf)

(define (state ctrl kaddr) (list 'state ctrl kaddr))
(define (appf evald unevald kaddr) (list 'appf evald unevald kaddr))
(define (addf evald unevald kaddr) (list 'addf evald unevald kaddr))
(define (letf name body kaddr) (list 'letf name body kaddr))
(define (iff et ef kaddr) (list 'iff et ef kaddr))
(define (carf kaddr) (list 'carf kaddr))
(define (cdrf kaddr) (list 'cdrf kaddr))

(define (abstraction? exp)
  (match exp
    [`(λ ,_ ,_) #t]
    [else #f]))

(define (concrete-value? v)
  (match v
    [(? boolean?) #t]
    [(? number?) #t]
    [(? abstraction?) #t]
    [(? list?) (andmap concrete-value? v)]
    [else #f]))
