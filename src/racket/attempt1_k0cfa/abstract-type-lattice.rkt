#lang racket

(provide abstract-+ abstract-car abstract-cdr abstract-if abstract-app
         avalue? join-value bottom make-abstract abstractify avalue)

(require (only-in "utils.rkt"
                  state abstraction? concrete-value?
                  appf addf letf iff carf cdrf))


; an abstract value in this lattice is
;   TOP
;    |
; typename
;    |
;  BOTTOM
;
; if the value is typename, its guaranteed that type in the concrete case.
; if its bottom the type is uninhabited somehow.... an error on Davis's part.
; if its top, we dont know which type itll be.
; TODO: I wonder if instead if it could be a powerset lattice of types here
;       then expressions like (not (number? x)) would work better...
;       but thats probably not too useful in practice. So 1 type for now.

(struct avalue (type abstractions) #:transparent)

(define top (avalue 'TOP (set)))
(define bottom (avalue 'BOTTOM (set)))

; takes a concrete value and turns it into an abstract value
(define (make-abstract v)
  (match v
    [`(λ ,args ,body) (avalue abstraction? (set `(λ ,args ,(abstractify body))))]
    [(? boolean?) (avalue boolean? (set))]
    [(? number?) (avalue number? (set))]
    ; TODO: how do we deal with (polymorphic?) types like lists,
    ; I feel like my (car xs) is just gonna return a TOP value... is that ok?
    ; or should it be more complex?
    [(? list?) (avalue list? (set))]
    [else (raise 'bad-value)]))


; turns all values in the expression into abstract values.
(define (abstractify e)
  (match e
    [(? concrete-value?) (make-abstract e)]
    [`(if ,ec ,et ,ef) `(if ,(abstractify ec) ,(abstractify et) ,(abstractify ef))]
    [`(let (,(? symbol? x) ,e) ,body) `(let (,x ,(abstractify e)) ,(abstractify body))]
    [`(+ ,es ...) `(+ ,@(map abstractify es))] ; should be covered by application case.
    [`(,ef ,es ...) `(,(abstractify ef) ,@(map abstractify es))]
    [(? symbol?) e]))

(define (join-value v1 v2)
  (match-define (avalue v1type v1abstrs) v1)
  (match-define (avalue v2type v2abstrs) v2)
  ; cause my match expression wasnt working for some reason
  (if (eq? v1type 'BOTTOM) (avalue v2type (set-union v1abstrs v2abstrs))
      (if (eq? v2type 'BOTTOM) (avalue v1type (set-union v1abstrs v2abstrs))
          (if (equal? v1type v2type) (avalue v1type (set-union v1abstrs v2abstrs))
              (avalue 'TOP (set-union v1abstrs v2abstrs))))))

;
; abstract function implementations.
;

(define (abstract-+ args next-kaddr)
  (list
   (state (foldl (λ (n accum)
                   (match-define (avalue ntype nabstrs) n)
                   (match-define (avalue accumtype accumabstrs) accum)
                   (if (and (eq? number? ntype) (eq? number? accumtype))
                       accum
                       (avalue 'TOP (set-union nabstrs accumabstrs))))
                 (make-abstract 0) args) next-kaddr)))

; uhhhh... not sure what todo here.
(define (abstract-car xs next-kaddr)
  (match-define (avalue _ abstrs) xs)
  (list (state (avalue 'TOP abstrs) next-kaddr)))

(define (abstract-cdr xs next-kaddr)
  (match-define (avalue _ abstrs) xs)
  (list (state (avalue 'TOP abstrs) next-kaddr)))

(define (abstract-if ctrl et ef next-kaddr)
  (list (state et next-kaddr)
        (state ef next-kaddr)))

(define (abstract-app args next-kaddr update-store)
  (match-define (avalue type abstrs) (car args))
  (set-map abstrs
           (λ (fn) (match fn
                     [`(λ (,fnargs ...) ,fnbody)
                      (define zipped (map cons fnargs (cdr args)))
                      (for-each update-store zipped)
                      (state fnbody next-kaddr)]
                     [else (displayln abstrs) (raise 'not-given-abstraction-somehow)]))))





















