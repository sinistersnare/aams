#lang racket

; compiles scheme code into relations, to be used as an EDB for datalog/slog

; supported relations:
(struct prog (id) #:transparent)
(struct lam (id formals body-id) #:transparent) ; a multi-arg lambda
(struct var (id formals-id formal-pos) #:transparent) ; a variable reference
(struct app (id args-id) #:transparent) ; a function application

(struct formal-param (id lam-id arg-pos) #:transparent) ; the parameter of a lambda
(struct app-arg (id app-pos arg-id) #:transparent) ; an argument in a lambda (could be the one in fn position)

; compiles a multi-argument lambda into relations.
; will output a list of 1 lambda relation, a relation for each formal parameter
; and the relations produced by the body.
(define (compile-lambda code cur-id env)
  (match-define `(λ (,formals ...) ,ebody) code)
  (define lam-id cur-id)
  (define formals-id (+ cur-id 1))
  (define next-id (+ cur-id 2))
  (define formal-params (map (λ (i) (formal-param formals-id lam-id i)) (range (length formals))))
  (define body-env (foldl (λ (fp-id argname res-env) (hash-set res-env argname fp-id))
                          env
                          (map (λ (fp) (match-define (formal-param fp-id _ pos) fp) (cons fp-id pos)) formal-params)
                          formals))
  (match-define (cons body-rels done-id) (do-compile ebody next-id body-env))
  (cons `(,(lam lam-id formals-id next-id) ,@formal-params ,@body-rels)
        done-id))

(define (compile-var code n env)
  (match-define (cons fp-id pos) (hash-ref env code))
  (cons (list (var n fp-id pos))
        (+ n 1)))

; compiles an untagged application, something like (f a b c)
; Returns a list containing an app relation,
; and an app-arg relation for each argument (including the function part)
(define (compile-untagged-application code cur-id env)
  (match-define `(,es ...) code)
  (define app-id cur-id)
  (define args-id (+ cur-id 1))
  (match-define (list compiled-rels done-n _num-args)
    (foldl (λ (arg res)
             (match-define (list mid-rels mid-id cur-pos) res)
             (match-define (cons arg-rels next-n) (do-compile arg mid-id env))
             `((,@mid-rels ,(app-arg args-id cur-pos mid-id) ,@arg-rels)
               ,next-n ,(+ cur-pos 1)))
           (list (list (app app-id args-id))
                 (+ cur-id 2)
                 0)
           es))
  (cons compiled-rels done-n))

; returns a list of relations given scheme
(define (do-compile code n env)
  (match code
    [`(λ ,_ ,_) (compile-lambda code n env)]
    [`(,_ ...) (compile-untagged-application code n env)]
    [(? symbol?) (compile-var code n env)]))

(define (compile code)
  (cons (prog 0) (car (do-compile code 0 (hash)))))

#;(pretty-display (compile '((λ (x y) (x y y)) (λ (x y) (x y y)) (λ (x y) (x y y)))))
#; (program
    (app (lam "x" "y" (app (ref "x") (ref "x") (ref "y")))
         (lam "x" "y" (app (ref "y") (ref "x") (ref "y")))
         (lam "x" "y" (app (ref "x") (ref "y") (ref "x")))))

(pretty-display (compile '((λ (x y) (x x y))
                           (λ (x y) (y x y))
                           (λ (x y) (x y x)))))
