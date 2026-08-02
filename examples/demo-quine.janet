(import ../kanja :as k)
(import ./interpreter :as i)

(defn- ms [f] (let [t0 (os/clock)] (let [r (f)] [r (math/round (* 1000 (- (os/clock) t0)))])))

(print "\n── BACKWARDS: which programs yield the value :target ──")
(let [[r t] (ms (fn [] (map i/show (k/run 3 [q] (i/evalo q :target)))))]
  (each x r (printf "   %s" x))
  (printf "   (%d ms)" t))

(print "\n── 🔴 QUINE: a program that evaluates to ITSELF ──")
(print "   We ask: name an exp such that evalo(exp) = exp.")
(let [[r t] (ms (fn [] (map i/show (k/run 1 [q] (i/evalo q q)))))]
  (each x r (printf "\n   %s" x))
  (printf "\n   (%d ms)" t))
