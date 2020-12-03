(prim +
 ((λ x (let ([a (prim car x)]) (prim * a a)))
  3 2 1)
 ((λ x (apply-prim * x)) 1 2 3 4 5))
; expect 129 as output
