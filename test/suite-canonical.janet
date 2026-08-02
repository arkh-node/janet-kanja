# Canonical relations, as taught in "The Reasoned Schemer".
#
# These are the relations every miniKanren is expected to support, written the
# way the book writes them. Expected answers are stated from the canonical
# semantics — what these relations mean — not copied from this engine's output.
# If the engine and the canon disagree, this suite must fail.

(import ../kanja :as k)
(import ../kanja/relations :prefix "")
(import ./harness :as h)

(h/start-suite "canonical")

(def- _0 (symbol "_.0"))
(def- _1 (symbol "_.1"))
(defn- arr [xs] (map k/to-array xs))

### ── pairs ──────────────────────────────────────────────────────────────────


(h/check "caro takes the head"
         (k/run* [q] (caro (k/llist :a :c :o :r :n) q)) @[:a])
(h/check "cdro takes the tail"
         (arr (k/run* [q] (cdro (k/llist :a :c :o :r :n) q))) @[@[:c :o :r :n]])
(h/check "caro runs BACKWARDS: which list starts with :a"
         (arr (k/run 1 [q] (caro q :a))) @[@[:a '& _0]])
(h/check "conso puts together"
         (arr (k/run* [q] (conso :a (k/llist :b :c) q))) @[@[:a :b :c]])
(h/check "conso takes apart: what the head was"
         (k/run* [q] (conso q (k/llist :b :c) (k/llist :a :b :c))) @[:a])
(h/check "nullo on the empty list" (k/run* [q] (nullo k/NIL) (k/== q :yes)) @[:yes])
(h/check "nullo on a non-empty list" (k/run* [q] (nullo (k/llist 1)) (k/== q :yes)) @[])
(h/check "pairo on a pair" (k/run* [q] (pairo (k/llist 1 2)) (k/== q :yes)) @[:yes])
(h/check "pairo on the empty list" (k/run* [q] (pairo k/NIL) (k/== q :yes)) @[])
(h/check "pairo on an atom" (k/run* [q] (pairo :atom) (k/== q :yes)) @[])

### ── lists ──────────────────────────────────────────────────────────────────

(h/check "listo on a proper list"
         (k/run* [q] (listo (k/llist 1 2 3)) (k/== q :yes)) @[:yes])
(h/check "listo on a variable tail: the first three lists built out"
         (arr (k/run 3 [q] (listo (k/llist* 1 2 q))))
         @[@[] @[_0] @[_0 _1]])

(h/check "membero enumerates every member"
         (k/run* [q] (membero q (k/llist :hummus :with :pita))) @[:hummus :with :pita])
(h/check "membero checks membership"
         (k/run* [q] (membero :with (k/llist :hummus :with :pita)) (k/== q :present)) @[:present])
(h/check "membero on absence"
         (k/run* [q] (membero :absent (k/llist :hummus :with :pita)) (k/== q :present)) @[])
(h/check "membero BACKWARDS: what the hole must be for :e to be inside"
         (k/run 1 [x] (membero :e (k/llist :pasta x :fagioli))) @[:e])

### ── appendo, and what makes it interesting ─────────────────────────────────

(defn appendo
  "`out` is `l` followed by `s`."
  [l s out]
  (k/conde
    [(nullo l) (k/== s out)]
    [(k/fresh [a d res]
       (conso a d l)
       (conso a res out)
       (appendo d s res))]))

(h/check "appendo forwards"
         (arr (k/run* [q] (appendo (k/llist :a :b) (k/llist :c :d) q)))
         @[@[:a :b :c :d]])
(h/check "appendo: every split — exactly length+1 of them"
         (length (k/run* [q] (k/fresh [x y] (appendo x y (k/llist 1 2 3 4 5)))))
         6)
(h/check "appendo with both unknown: the first answers, canonical shape"
         (arr (k/run 3 [q] (k/fresh [x y] (appendo x y (k/llist :a :b))
                                          (k/== q (k/llist x y)))))
         @[@[@[] @[:a :b]] @[@[:a] @[:b]] @[@[:a :b] @[]]])

### ── rembero: removal, and the subtlety the book stops on ──────────────────

(defn rembero
  "`out` is `l` with the first occurrence of `x` removed."
  [x l out]
  (k/conde
    [(nullo l) (k/== out k/NIL)]
    [(k/fresh [a d] (conso a d l) (k/== a x) (k/== out d))]
    [(k/fresh [a d res]
       (conso a d l) (k/=/= a x)
       (conso a res out)
       (rembero x d res))]))

# The same relation as the book writes it — WITHOUT the prohibition in the
# third branch. This is where the book stops: without `=/=` the third branch
# also applies when the head EQUALS what is sought, so "remove the first
# occurrence" falls apart into "remove any" plus "remove none at all".
(defn rembero-naive [x l out]
  (k/conde
    [(nullo l) (k/== out k/NIL)]
    [(k/fresh [a d] (conso a d l) (k/== a x) (k/== out d))]
    [(k/fresh [a d res]
       (conso a d l)
       (conso a res out)
       (rembero-naive x d res))]))

(h/check "rembero removes the first occurrence"
         (arr (k/run* [q] (rembero :b (k/llist :a :b :c) q)))
         @[@[:a :c]])
(h/check "with the prohibition there is EXACTLY one answer"
         (length (k/run* [q] (rembero :b (k/llist :a :b :c :b) q)))
         1)
(h/check "without the prohibition there are more answers — that is what =/= buys"
         (arr (k/run* [q] (rembero-naive :b (k/llist :a :b :c :b) q)))
         @[@[:a :c :b] @[:a :b :c] @[:a :b :c :b]])

### ── numbers as lists of bits (canonical arithmetic, smallest case) ────────
# The classic way to do arithmetic relationally: numbers are little-endian
# lists of bits. Included here to prove the engine handles the shape, not to
# ship an arithmetic library.

(defn bit-xoro [x y r]
  (k/conde
    [(k/== 0 x) (k/== 0 y) (k/== 0 r)]
    [(k/== 1 x) (k/== 0 y) (k/== 1 r)]
    [(k/== 0 x) (k/== 1 y) (k/== 1 r)]
    [(k/== 1 x) (k/== 1 y) (k/== 0 r)]))

(h/check "xor forwards" (k/run* [q] (bit-xoro 1 1 q)) @[0])
(h/check "xor backwards: which pairs yield 1"
         (k/run* [q] (k/fresh [x y] (bit-xoro x y 1) (k/== q [x y])))
         @[[1 0] [0 1]])

(h/finish)
