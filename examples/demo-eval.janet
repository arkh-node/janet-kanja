(import ../kanja :as k)
(import ./interpreter :as i)
(defn ev [prog] (string/join (map i/show (k/run 1 [q] (i/evalo prog q))) " "))
(printf "1. (quote :hello)               -> %s" (ev (k/llist 'quote :hello)))
(printf "2. (list (quote 1) (quote 2))    -> %s"
        (ev (k/llist 'list (k/llist 'quote 1) (k/llist 'quote 2))))
(printf "3. ((lambda (x) x) (quote :yes))  -> %s"
        (ev (k/llist (k/llist 'lambda (k/llist 'x) 'x) (k/llist 'quote :yes))))
