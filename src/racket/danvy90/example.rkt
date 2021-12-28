#lang racket
(require racket/control)


(define flip
  (lambda () (shift c (begin (c #t) (c #f) (fail)))))

(define fail
  (lambda () (shift c "no")))
;(define (fail) "no")

(define (choice n)
  (if (< n 1)
        (fail)
        (if (flip 5) (choice (- n 1)) n)))


(define triple
  (lambda (n s)
    (let* ([i (choice n)]
           [j (choice (- i 1))]
           [k (choice (- j 1))])
      (if (= (+ i j k) s)
          (list i j k)
          (fail)))))

#;(reset (displayln (triple 9 6)))
#;(+ 1 (reset (+ 10 (shift c (c (c 100))))))
(+ 1 (reset (shift c (+ 10 (c (c 100))))))
