# The closing condition of step 8: the machine GENERATES a program, and what
# it generated, run forwards, yields itself. Checked by comparison, not by eye.
(import ../kanja :as k)
(import ../examples/interpreter :as i)

(def t0 (os/clock))
(def [ans] (k/run 1 [q] (i/evalo q q)))
(def prog (if (and (indexed? ans) (= 'quote (get-in ans [0 0] nil))) ans (get ans 0 ans)))
(printf "generated in %d ms" (math/round (* 1000 (- (os/clock) t0))))

# in an answer carrying demands, the first element is the program itself
(def Q (if (and (tuple? ans) (> (length ans) 1) (indexed? (ans 0))) (ans 0) ans))
(printf "\nGENERATED PROGRAM:\n  %s" (k/show Q))

(def out (k/run 1 [v] (i/evalo Q v)))
(printf "\nTHE SAME, EVALUATED FORWARDS:\n  %s" (k/show (first out)))
# DATA is compared, not printed strings: two different things can print
# identically, and then the check would stop checking.
(def same (deep= (k/to-array Q) (k/to-array (first out))))
(printf "\nTHEY MATCH: %s" (if same "YES — it is a quine" "NO"))
(os/exit (if same 0 1))
