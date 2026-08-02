(import ../kanja :as k)
(import ../examples/interpreter :as i)
(defn- ms [f] (let [t0 (os/clock)] (let [r (f)] [r (math/round (* 1000 (- (os/clock) t0)))])))
(defn try [name f]
  (let [[r t] (ms f)] (printf "%-46s %6d ms  %s" name t (string/join r " "))))
(try "synthesis: a program yielding the list (1 2)"
     (fn [] (map i/show (k/run 1 [q] (i/evalo q (k/llist 1 2))))))
(try "synthesis: one yielding (quote x) inside a list"
     (fn [] (map i/show (k/run 1 [q] (i/evalo q (k/llist 'quote 5))))))
(try "check: the known quine evaluates to itself"
     (fn []
       (def Q (k/llist
                (k/llist 'lambda (k/llist 'x)
                  (k/llist 'list 'x (k/llist 'list (k/llist 'quote 'quote) 'x)))
                (k/llist 'quote
                  (k/llist 'lambda (k/llist 'x)
                    (k/llist 'list 'x (k/llist 'list (k/llist 'quote 'quote) 'x))))))
       (map i/show (k/run 1 [q] (i/evalo Q q)))))
