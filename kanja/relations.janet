### Classic relations, as taught in "The Reasoned Schemer".
###
### They are shipped rather than left in the tests because they are the
### vocabulary every miniKanren user already knows, and because a reader
### learns more from `appendo` than from any description of unification.

(import ./init :as k)

(defn caro   "`a` is the head of `p`."        [p a] (k/fresh [d] (k/== (k/cons* a d) p)))
(defn cdro   "`d` is the tail of `p`."        [p d] (k/fresh [a] (k/== (k/cons* a d) p)))
(defn conso  "`p` is `a` prepended to `d`."   [a d p] (k/== (k/cons* a d) p))
(defn nullo  "`x` is the empty list."         [x] (k/== x k/NIL))
(defn pairo  "`x` is a pair."                 [x] (k/fresh [a d] (conso a d x)))

(defn listo
  "`l` is a proper list — it ends in the empty list."
  [l]
  (k/conde
    [(nullo l)]
    [(k/fresh [d] (cdro l d) (listo d))]))

(defn membero
  ``x occurs in list l.

  Runs both ways: ask for `x` and it enumerates the members; ask for `l` and
  it builds lists containing `x`.``
  [x l]
  (k/conde
    [(k/fresh [d] (conso x d l))]
    [(k/fresh [a d] (conso a d l) (membero x d))]))

(defn appendo
  ``out is l followed by s.

  The relation every introduction starts with, because it is the shortest way
  to see that a relation has no input side: the same definition joins two
  lists, takes one apart, and enumerates every way a list could have been
  split in two.``
  [l s out]
  (k/conde
    [(nullo l) (k/== s out)]
    [(k/fresh [a d res]
       (conso a d l)
       (conso a res out)
       (appendo d s res))]))

(defn rembero
  ``out is l with the first occurrence of x removed.

  The `=/=` in the last branch is what makes it the FIRST occurrence rather
  than any occurrence: without it the relation also answers "remove a later
  one" and "remove none at all".``
  [x l out]
  (k/conde
    [(nullo l) (k/== out k/NIL)]
    [(k/fresh [a d] (conso a d l) (k/== a x) (k/== out d))]
    [(k/fresh [a d res]
       (conso a d l) (k/=/= a x)
       (conso a res out)
       (rembero x d res))]))
