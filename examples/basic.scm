(let ([square (lambda (x) (prim * x x))]
	  [cube (lambda (x) (prim * x x x))]) (square (cube 2)))
; expect 64 as output
