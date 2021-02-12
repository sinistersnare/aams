#lang racket

; compiles scheme code into relations, to be used as an EDB for datalog/slog

; supported relations:
(struct prog (id) #:transparent)
(struct lam (id x-id y-id body-id) #:transparent)
(struct var (id which-id) #:transparent)
(struct app (id arg0-id arg1-id arg2-id) #:transparent)

(define (compile-lambda code n env)
  (match-define `(λ (,x ,y) ,e) code)
  (define lam-id n)
  (define x-id (+ n 1))
  (define y-id (+ n 2))
  (define next-id (+ n 3))
  (match-define (cons rest-rels done-n) (do-compile e next-id (hash-set (hash-set env x x-id) y y-id)))
  (cons (cons (lam lam-id x-id y-id next-id) rest-rels)
        done-n))

(define (compile-var code n env)
  (cons (list (var n (hash-ref env code)))
        (+ n 1)))

(define (compile-app code n env)
  (match-define `(,es ...) code)
  (define app-id n)
  (match-define (list arg-rels next-n arg-ids)
    (foldl (λ (arg res)
             (match-define (list mid-rels mid-n mid-ids) res)
             (match-define (cons arg-rels next-n) (do-compile arg mid-n env))
             (list (append mid-rels arg-rels) next-n (append mid-ids (list mid-n))))
           (list '() (+ n 1) '()) es))
  (cons (cons (apply app (cons app-id arg-ids)) arg-rels)
        next-n))

; returns a list of relations given scheme
(define (do-compile code n env)
  (match code
    [`(λ ,_ ,_) (compile-lambda code n env)]
    [`(,_ ...) (compile-app code n env)]
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
