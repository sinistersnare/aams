(+
 ((λ x (let ([a (car x)]) (* a a)))
  3 2 1)
 ((λ x (apply * x)) 1 2 3 4 5))
; expect 129 as output
