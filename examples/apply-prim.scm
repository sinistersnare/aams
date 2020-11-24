; apply-prim is similar to prim
(apply-prim + ; apply-prim takes a list
	; lists must be null terminated.
; Im also testing that comments work correctly here.
	(prim cons 1 (prim cons 2 (prim cons 3 (prim cons 4 (prim null))))))
