(apply + ; apply takes a list
; lists must be null terminated.
; Im also testing that comments work correctly here.
	(cons 1 (cons 2 (cons 3 (cons 4 (null))))))
; expect 10 as output

((lambda (square cube) (square (cube 2)))
	(lambda (x) (* x x))
	(lambda (x) (* x x x)))
