(let ([square (lambda (x) (* x x))]
	  [cube (lambda (x) (* x x x))]) (square (cube 2)))
; expect 64 as output
