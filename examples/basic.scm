(let ([square (lambda (x) (prim * x x))]
	  [cube (lambda (x) (prim * x x x))]) (square (cube 2)))
