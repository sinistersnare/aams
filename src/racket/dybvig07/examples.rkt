#lang racket

(require racket/control)


;;;;; Examples showing how the prompt can be taken from the stack
;;;;; and what that may cause.
;;;;; This example is most prevalent in -F-, as there is a net
;;;;; loss of 1 prompt on the stack after -F- is used.
;;;;; This means that -F- is not purely functional!
;;;;; The other operators work in this example because they re-add the prompt at some point.
;;;;; (that is, -F+ does it after calling the k, the others never take it away in the first place)

; -F- does not work in this case, beacuse cupto/spawn/withSubCont
; removes the prompt when working, and it is never restored.
#;
((λ (p) (set p (+ (cupto p k (k 3))
                  (cupto p k (k 4)))))
 (new-prompt))

; this example uses -F+ (spawn from Hieb & Dybvig 90)
; we can use the prompt again here as it is replaced when
; the first continuation is reinstated.
#;
(spawn (λ (p) (+ (p (λ (k) (k 3)))
                 (p (λ (k) (k 4))))))

; not sure this does what we want really? Considering
; that `p` pushes the prompt, so its being pushed twice?
; but the example utilizing -F+ directly (not runnable in racket)
; has the same output (when tested in cekm.rkt)

;;;;
; Have the prompt escape so -F+ wont work if its not reinstated.
;;;;
#;
(spawn (λ (p) (+ (p (λ (k) 3))
                 (p (λ (k) (k 4))))))


; this doesnt work because the first -F+ fully aborts the continuation,
; which includes the second -F+ call, so its never used.
#;
((λ (p) (pushPrompt p (+ 1
                         (-F+ p (λ (k) 3))
                         (-F+ p (λ (k) (k 3))))))
 (newPrompt))

#;
(+ 1 ((λ (p) (pushPrompt p (+ 1
                         (-F+ p (λ (k) 3))
                         (-F+ p (λ (k) (k 3))))))
 (newPrompt)))

; +F- works because the prompt is left on the stack when control-at is called
; so we can call it again.
#;
((λ (p) (prompt-at p (+ (control-at p k (k 3))
                        (control-at p k (k 4)))))
 (new-prompt))

; +F+ works here, because it leaves the prompt on the stack, so we can shift-at again!
#;
((λ (p) (reset-at p (+ (shift-at p k (k 3))
                       (shift-at p k (k 4)))))
 (new-prompt))




;;;;; Worrying about the second +- is about if the prompt gets
;;;;; reinstated after reinstating the continuation.

;; works on cekm.rkt machine.
#;
((λ (p) (pushPrompt p (+ 1
                         (-F+ p (λ (k) (k (-F- p (λ (k2) (k2 5)))))))))
 (newPrompt))

;;; Handler Examples ;;

(require "cekm.rkt")

;; simple examples of straight -F- Delimited Continuation usage.
#;
(run '((λ (p) (pushPrompt p (withSubCont p (λ (k) (+ 1 (pushSubCont k 5)))))) (newPrompt)))
#;
(run '((λ (p) (pushPrompt p (+ 1 (withSubCont p (λ (k) (+ 2 1)))))) (newPrompt)))


; evaluates to 6, as the 10000+[] is escaped from before it can be evaluated.
(define basic-example
  '(+ 1 (call/handler ([throw (λ (_ x) x)])
                      (λ (h) (+ 10000 (perform throw h 5))))))

;; This example shows why handlers need at least +F semantics.
;; When `withSubCont` is called by the outer throw performance,
;; the prompt is taken off the stack (as the underlying DC impl is -F-).
;; So the handler must re-place the prompt so the inner `read`
;; performance can happen.
;;
;; Example of a simple effect handler
;;
;; This expr returns 3 as the 9+[] is escaped from before it can be evaluated.
(define inner-perform-example
  '(+ 1 (call/handler ([throw (λ (_ x) x)] [read (λ (k) (k 1))])
                      (λ (h) (+ 9 (perform throw h (+ 1 (perform read h))))))))

;; This example shows why we need at least F+ semantics.
;; The handlers here escape the context, but also keep around a reference to the
;; continuation, so it can be executed by the argument (`4` in this case).
;; However, when the handler is reinstated, the prompt is gone
;; So we need F+ semantics to re-place the prompt when a continuation is called.
;;
;; Example of local state with an effect handler.
;; get and set abort, only to later reinstate with the state value.
;;
;; This example returns 25, as the original state is saved, then changed and
;; the two values are summed.
(define leaving-context-example
  '((call/handler ([get (λ (k) (λ (s) ((k s) s)))]
                   [set (λ (k x) (λ (s) ((k 'void) x)))])
                  (λ (h) (let ([x (perform get h)])
                           (let ([_ (perform set h 21)])
                             (λ (state) (+ x state))))))
    4))

#;
(run basic-example)
#;
(run inner-perform-example)
#;
(run leaving-context-example)
