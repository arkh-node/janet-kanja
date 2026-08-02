###
### kanren — relational programming for Janet
###
### An embedding of miniKanren: pure relations, complete interleaving search.
### The core follows µKanren (Hemann & Friedman, Scheme Workshop 2013); the
### surface follows miniKanren as presented in "The Reasoned Schemer"
### (Friedman, Byrd, Kiselyov; MIT Press).
###
### A relation is not a function: it has no designated input or output. The same
### definition answers "combine these two" and "which pairs combine into this".
###

(def version
  ``Version of this library. Kept here because the banner and any caller need
  it at runtime; `project.janet` holds the same string for `jpm`, and the two
  must be moved together.``
  "0.1.0-dev")

### ── Logic variables ────────────────────────────────────────────────────────

(def- VAR :kanja/var)
(def- PAIR :kanja/pair)

(defn lvar
  ``Make a fresh logic variable with index `n`.

  A logic variable stands for a value that is not known yet. It is not a
  mutable cell: it is either unbound, or bound once by unification within a
  particular substitution. Different branches of the search hold different
  substitutions, so the same variable may be bound differently in each.``
  [n]
  [VAR n])

(defn lvar?
  "True if `x` is a logic variable."
  [x]
  (and (tuple? x) (= 2 (length x)) (= VAR (x 0))))

# lvar is [VAR n] of length 2; keep the representation in one place.
(defn- mk-var [n] [VAR n])
(defn- var? [x] (and (tuple? x) (= 2 (length x)) (= VAR (x 0))))
(defn- var-index [x] (x 1))

### ── Pairs: lists whose tail may be unknown ─────────────────────────────────
###
### Janet tuples and arrays are fixed-length, so they cannot express "a list
### that starts with 1 and continues with something not yet known". Relations
### need exactly that, so `kanren` carries its own pairs. Native tuples and
### arrays still unify element-wise (see `unify`), so ordinary Janet data can
### be used directly wherever its shape is known.

(def NIL
  "The empty list."
  :kanja/nil)

(defn cons*
  "Pair `h` (head) with `t` (tail). The tail may be a logic variable."
  [h t]
  [PAIR h t])

(defn pair?
  "True if `x` is a kanren pair."
  [x]
  (and (tuple? x) (= 3 (length x)) (= PAIR (x 0))))

(defn llist
  "Build a kanren list from the given elements: `(llist 1 2 3)`."
  [& xs]
  (var acc NIL)
  (each x (reverse xs) (set acc (cons* x acc)))
  acc)

(defn llist*
  ``Build a list whose TAIL is the last argument: `(llist* 1 2 t)` is the list
  that starts with 1 and 2 and continues with whatever `t` turns out to be.

  This is the shape a fixed-length Janet tuple cannot express, and the reason
  relations need their own pairs at all.``
  [& xs]
  (assert (not (empty? xs)) "llist* needs at least the tail")
  (var acc (last xs))
  (each x (reverse (slice xs 0 -2)) (set acc (cons* x acc)))
  acc)

(defn to-array
  ``Convert a kanren list to a Janet array, for printing and for handing the
  answer back to ordinary code. An unbound tail is kept as-is at the end.``
  [v]
  (cond
    (= NIL v) @[]
    (pair? v) (let [head (to-array (v 1))
                    rest (to-array (v 2))]
                (if (array? rest)
                  (array/concat @[head] rest)
                  @[head '& rest]))
    (tuple? v) (tuple ;(map to-array v))
    (array? v) (array ;(map to-array v))
    v))

### ── Substitution and walking ───────────────────────────────────────────────

### A substitution is a MAP from variable index to value.
###
### The choice is forced by measurement, not by taste. Relational search READS
### the substitution far more often than it writes it: every occurrence of
### every variable in every goal is a lookup. A chain gives O(1) writes but
### O(N) reads, and that trade loses badly — measured against a canonical
### implementation on the same task, a chain-based `walk` did 1.5 million scans
### while the canon needed 41 thousand, and the search never got off the
### ground. Reads must be cheap first.
###
### The key is the variable's index, an integer, not the variable tuple:
### hashing a small integer is cheaper than hashing a tuple, and this lookup is
### the hottest operation in the library.

(def- EMPTY-S {})

# Failure needs its OWN representation, distinct from emptiness.
# nil already means "this state is illegal"; a store with nothing in it is not
# an illegal state. Sharing one shape between "nothing yet" and "cannot be"
# made the very first `=/=` look like a contradiction.
(def- FAIL :kanja/violated)

(defn walk
  ``Follow `u` through substitution `s` until an unbound variable or a
  non-variable term is reached. This is what makes a variable transparent:
  code never sees the variable, it sees whatever the variable stands for.``
  [u s]
  (if (var? u)
    (let [hit (in s (u 1))]
      (if (= nil hit) u (walk hit s)))
    u))

(defn- occurs?
  ``Does variable `x` occur anywhere inside term `v`?

  Asked before every binding. Not a safety nicety: a relational interpreter
  run backwards necessarily steers the search into `v := (quote v)` and the
  like, and a binding that builds such a circular term does not fail — it
  makes every later traversal of that term (unification, `absento`, reading
  the answer) recurse forever. The engine then looks like a memory leak while
  in fact it is one call that never returns.``
  [x v s]
  (let [v (walk v s)]
    (cond
      (var? v) (= v x)
      (pair? v) (or (occurs? x (v 1) s) (occurs? x (v 2) s))
      (indexed? v) (do (var res false)
                       (each e v (when (occurs? x e s) (set res true)))
                       res)
      false)))

(defn- ext-s
  "Bind `x` to `v`, or fail (nil) if that would make `x` contain itself."
  [x v s]
  (if (occurs? x v s) nil (struct ;(kvs s) (x 1) v)))

(defn- chain->array
  "Read a chain back into an array, newest first."
  [ch]
  (def out @[])
  (var c ch)
  (while (not (empty? c)) (array/push out (c 0)) (set c (c 1)))
  out)

(defn- array->chain [xs]
  (var c [])
  (each x (reverse xs) (set c [x c]))
  c)

(defn- chain-get
  "First value stored for `k` in the chain, or nil."
  [ch k]
  (var c ch)
  (var res nil)
  (while (and (not (empty? c)) (nil? res))
    (if (= ((c 0) 0) k) (set res ((c 0) 1)) (set c (c 1))))
  res)



(defn unify
  ``Reconcile `u` with `v` under substitution `s`.

  Returns an extended substitution, or nil if the two cannot be reconciled.
  Unification is symmetric — there is no input side and no output side, which
  is precisely why relations run in every direction.

  Unifies: logic variables · kanren pairs · Janet tuples and arrays of equal
  length, element-wise · everything else by `=`.

  Occurs check on every binding, as faster-minikanren does it (`ext-s-check`,
  mk.scm:249). Binding a variable to a term that contains that same variable
  FAILS cleanly instead of building a circular term, so `(== q (cons* q q))`
  now honestly has no answers. The check costs a traversal per binding and
  buys the ability to run an interpreter backwards at all.``
  [u v s]
  (let [u (walk u s) v (walk v s)]
    (cond
      (and (var? u) (var? v) (= u v)) s
      (var? u) (ext-s u v s)
      (var? v) (ext-s v u s)
      (and (pair? u) (pair? v))
        (let [s1 (unify (u 1) (v 1) s)]
          (and s1 (unify (u 2) (v 2) s1)))
      (and (indexed? u) (indexed? v) (= (length u) (length v)))
        (do (var acc s)
            (var i 0)
            (while (and acc (< i (length u)))
              (set acc (unify (in u i) (in v i) acc))
              (++ i))
            acc)
      (= u v) s
      nil)))

(defn- walk*
  ``Walk `v` and everything inside it, so the result contains no variable that
  the substitution can resolve. Used wherever a term must be compared or shown
  as a whole rather than followed one link at a time.``
  [v s]
  (let [v (walk v s)]
    (cond
      (pair? v) (cons* (walk* (v 1) s) (walk* (v 2) s))
      (tuple? v) (tuple ;(map (fn [x] (walk* x s)) v))
      (array? v) (array ;(map (fn [x] (walk* x s)) v))
      v)))

(defn- unify+
  ``Like `unify`, but also reports which bindings were *added*.

  Disequality needs this: to say "these two must never become equal" is to
  forbid exactly the set of bindings that would make them equal. That set is
  the growth of the substitution, and nothing else.

  Returns [s' added] or nil.``
  [u v s]
  (var added [])            # chain, not a table: same reason as the state
  (defn go [u v s]
    (let [u (walk u s) v (walk v s)]
      (cond
        (and (var? u) (var? v) (= u v)) s
        (var? u) (do (set added [[u v] added]) (ext-s u v s))
        (var? v) (do (set added [[v u] added]) (ext-s v u s))
        (and (pair? u) (pair? v))
          (let [s1 (go (u 1) (v 1) s)] (and s1 (go (u 2) (v 2) s1)))
        (and (indexed? u) (indexed? v) (= (length u) (length v)))
          (do (var acc s) (var i 0)
              (while (and acc (< i (length u)))
                (set acc (go (in u i) (in v i) acc)) (++ i))
              acc)
        (= u v) s
        nil)))
  (let [s2 (go u v s)]
    (if s2 [s2 added] nil)))

### ── State ──────────────────────────────────────────────────────────────────
###
### A state carries three things: what is known (the substitution), how many
### variables have been made (the counter), and what is FORBIDDEN (the
### disequality store). The third is why `=/=` is not simply "unify and fail":
### a prohibition has to outlive the moment it was stated and fire later, when
### some other goal finally makes the forbidden binding.

(defn- st
  ``Build a state: what is known · how many variables exist · what is
  forbidden · what types are demanded · what must stay absent.

  The last three are constraint stores. They exist because a constraint is not
  a test: it is stated at a moment when it can be neither confirmed nor
  refuted, and it has to wait until some later goal decides it.``
  [s c d types absent]
  # A positional tuple, not a struct with named keys. Measured in Janet:
  # allocating 200k five-key structs takes ~358 ms, five-field tuples ~31 ms —
  # an order of magnitude. A state is built at every step of the search, so
  # this is the hottest allocation in the library. Readability is kept by the
  # accessors below, which are the only places that know about positions.
  [s c d types absent])

(defn- st-s [x] (x 0))
(defn- st-c [x] (x 1))
(defn- st-d [x] (x 2))
(defn- st-types [x] (x 3))
(defn- st-absent [x] (x 4))

(defn- verify-constraints
  ``Re-check every prohibition against a substitution that has just grown.

  Each prohibition is a set of bindings that must not all hold at once.
  Three outcomes per prohibition:
    · it can no longer be satisfied at all  → drop it, it is discharged;
    · it holds fully under the new knowledge → the state is illegal, fail;
    · it partly holds                        → keep what is still forbidden.``
  [d s]
  (var out [])
  (var ok true)
  (each c (chain->array d)
    (when ok
      (var acc s)
      (var added [])
      (var alive true)
      (each [k v] (chain->array c)
        (when alive
          (let [r (unify+ k v acc)]
            (if r
              (do (set acc (r 0))
                  (each pr (chain->array (r 1)) (set added [pr added])))
              (set alive false)))))       # unification impossible → discharged
      (cond
        (not alive) nil                    # drop
        (empty? added) (set ok false)      # fully entailed → violated
        (set out [added out]))))
  (if ok out FAIL))

(defn- type-holds?
  "Does concrete value `v` satisfy type tag `tag`?"
  [tag v]
  (case tag
    :symbol (or (symbol? v) (keyword? v))
    :number (number? v)
    false))

(defn- type-name [tag] (case tag :symbol "sym" :number "num" "?"))

(defn- verify-types
  ``Re-check demanded types against a substitution that has just grown.

  A variable that has since become concrete is checked and the demand is
  discharged. A variable still unbound keeps its demand. Two demands landing
  on the same variable must agree — nothing can be a symbol and a number.``
  [types s]
  (var out @{})
  (var ok true)
  (each [v tag] (chain->array types)
    (when ok
      (let [w (walk v s)]
        (cond
          (var? w) (let [had (in out w)]
                     (if (and had (not= had tag)) (set ok false) (put out w tag)))
          (type-holds? tag w) nil
          (set ok false)))))
  (if ok (array->chain (seq [[v tag] :pairs out] [v tag])) FAIL))

(defn- leaf-tag?
  ``True if `tag` is a leaf — neither a variable nor a compound term.

  A leaf can only ever meet another leaf, never a whole branch, so the
  expensive comparison below is not needed for it. This matters: every
  practical use of `absento` (the relational interpreter's `absento 'closure`
  among them) passes a leaf, and this is the hottest path in the store.``
  [tag]
  (and (not (var? tag)) (not (pair? tag)) (not (indexed? tag))))

(defn- meets?
  ``Can term `t`, taken WHOLE, be the same thing as `tag`?

  true — it already is · false — it never can be · :maybe — not settled yet.

  For a compound tag, `walk*` on both sides is what makes the first answer
  honest: two terms built from the same still-unbound variable are the same
  term, even though neither is known. `unify` decides the second — if the two
  cannot be reconciled, no later binding will make them equal.``
  [tag t s]
  (if (leaf-tag? tag)
    (cond
      (var? t) :maybe
      (= t tag) true
      false)
    (cond
      (= (walk* tag s) (walk* t s)) true
      (nil? (unify tag t s)) false
      :maybe)))

(defn- push-absento
  ``Spread the demand "`tag` occurs nowhere in `t`" down the term, and report
  what has to be remembered.

  Returns `[absent-pairs diseq-pairs]`, or nil if the demand is already broken.

  🔴 The decomposition is the canon's (`mk.scm:491`) and it is not the same at
  every kind of node:

  · a VARIABLE — the question stays open, because anything may still appear
    inside it. This is the only place an `absento` demand survives.
  · a COMPOUND node — the tag cannot be *inside* the node itself, only equal
    to it, so what remains here is a plain prohibition `node =/= tag`. With an
    atomic tag that prohibition is discharged on the spot (an atom is never a
    pair) and costs nothing at all.
  · an ATOM — decided immediately, one way or the other.

  Why bother: held whole, one demand costs a full traversal of its term on
  EVERY later `==`, and it prints as a wall — the quine carried three of them,
  each restating a large subterm, where the canon prints one pair. Pushed
  down, what survives sits on the variables alone.``
  [tag t s]
  (def absents @[])
  (def diseqs @[])
  (var ok true)
  (defn go [t]
    (when ok
      (let [t (walk t s)]
        (cond
          (var? t)
            (case (meets? tag t s)
              true (set ok false)
              false nil
              (array/push absents [tag t]))
          (or (pair? t) (indexed? t))
            (do
              # the node itself must not BE the tag
              (case (meets? tag t s)
                true (set ok false)
                false nil
                (array/push diseqs [tag t]))
              (when ok
                (if (pair? t)
                  (do (go (t 1)) (go (t 2)))
                  (each x t (go x)))))
          # an atom: settled here and now
          (when (= (meets? tag t s) true) (set ok false))))))
  (go t)
  (if ok [absents diseqs] nil))

(defn- verify-absent
  ``Re-check every absence demand; drop the settled, fail on the violated.

  A demand is re-spread on every check, not merely re-tested: the term it sits
  on grows as the search binds variables, and one open question can become
  several — or none. Any prohibition that falls out of the spreading is handed
  back to the caller, which owns the prohibition store.``
  [absent s]
  (def out @[])
  (def extra @[])
  (var ok true)
  (each [tag t] (chain->array absent)
    (when ok
      (let [r (push-absento tag t s)]
        (if r
          (do (array/concat out (r 0)) (array/concat extra (r 1)))
          (set ok false)))))
  (if ok [(array->chain (distinct out)) extra] FAIL))

(defn- add-diseq
  ``Add the prohibition "`u` is never `v`" to prohibition store `d`.
  Returns the new store, or FAIL if the two are already the same.

  The same three-way decision as the `=/=` goal, lifted out of it so that
  `absento`, when it spreads down a term, can put its leftovers in the store
  the store belongs to instead of growing a second one beside it.``
  [d u v s]
  (let [r (unify+ u v s)]
    (cond
      (nil? r) d                # never equal → nothing to forbid
      (empty? (r 1)) FAIL       # already equal → illegal
      [(r 1) d])))

(defn- add-diseqs
  "Add every prohibition in `pairs` to store `d`; FAIL if any is impossible."
  [d pairs s]
  (var acc d)
  (each [u v] pairs
    (unless (= acc FAIL) (set acc (add-diseq acc u v s))))
  acc)

### ── Streams ────────────────────────────────────────────────────────────────
###
### An answer stream is one of: nil (no answers) · a pair [answer rest] ·
### a function of no arguments (an answer that has not been computed yet).
### The last case is what lets a relation with infinitely many answers be
### written down and consumed a few answers at a time.

(var UNIFS "Counter: calls to ==, for measurement." 0)
(var PULLS "Counter: stream forcings, for measurement." 0)

(defn- mplus
  ``Merge two answer streams, alternating between them.

  The swap in the delayed case is the whole reason miniKanren's search is
  complete: no branch can starve another, so an answer that exists is always
  reached, even when a sibling branch is infinite. Depth-first search — the
  Prolog default — does not have this property.``
  # Canon signature (faster-minikanren `case-inf`): the second argument is
  # ALWAYS a thunk, and four cases are distinguished — empty · suspension ·
  # singleton · pair. A mature run longer than one element is then not merely
  # rare but UNREPRESENTABLE, so no single forcing can walk an unbounded tail.
  [strm f]
  (cond
    (nil? strm) (f)
    (function? strm) (fn [] (mplus (f) strm))
    (nil? (strm 1)) [(strm 0) f]
    [(strm 0) (fn [] (mplus (f) (strm 1)))]))

(defn- bind
  "Continue every answer of stream `strm` with goal `g`."
  [strm g]
  (cond
    (nil? strm) nil
    (function? strm) (fn [] (bind (strm) g))
    (nil? (strm 1)) (g (strm 0))
    (mplus (g (strm 0)) (fn [] (bind (strm 1) g)))))

(defn- pull
  "Force a stream until it is either empty or has an answer at the head."
  [strm]
  (if (function? strm) (do (++ PULLS) (pull (strm))) strm))

### ── Goals ──────────────────────────────────────────────────────────────────
###
### A goal is a function from a state to a stream of states. A state is
### [substitution counter].

(defn ==
  ``The goal that `u` and `v` denote the same thing.

  Succeeds with at most one answer — the substitution that reconciles them —
  and fails if they cannot be reconciled.``
  [u v]
  (fn [state]
    (++ UNIFS)
    (let [s2 (unify u v (st-s state))]
      (if (nil? s2)
        nil
        # Growth of knowledge can violate any standing constraint, so every
        # store is re-checked here. This is the one place where a promise made
        # earlier gets its chance to fire.
        (let [d2 (verify-constraints (st-d state) s2)]
          (if (= d2 FAIL) nil
            (let [t2 (verify-types (st-types state) s2)]
              (if (= t2 FAIL) nil
                (let [a2 (verify-absent (st-absent state) s2)]
                  (if (= a2 FAIL) nil
                    # Re-spreading `absento` can turn part of a demand into
                    # plain prohibitions; they go into the prohibition store,
                    # which may itself fail on them.
                    (let [d3 (add-diseqs d2 (a2 1) s2)]
                      (if (= d3 FAIL) nil
                        [(st s2 (st-c state) d3 t2 (a2 0)) nil]))))))))))))

(defn =/=
  ``The goal that `u` and `v` must never denote the same thing.

  Unlike a test, this is not decided on the spot. If the two are already
  distinct beyond repair, the goal simply succeeds. If they are already the
  same, it fails. Otherwise the prohibition is recorded and outlives this
  moment: it fires later, if some other goal ever makes the forbidden binding.``
  [u v]
  (fn [state]
    (let [r (unify+ u v (st-s state))]
      (cond
        (nil? r) [state nil]                          # never equal → nothing to forbid
        (empty? (r 1)) nil                            # already equal → illegal
        [(st (st-s state) (st-c state)
             [(r 1) (st-d state)]
             (st-types state) (st-absent state)) nil]))))

(defn- typeo
  "Shared body of `symbolo` and `numbero`."
  [tag x]
  (fn [state]
    (let [w (walk x (st-s state))]
      (cond
        (var? w)
          (let [had (chain-get (st-types state) w)]
            (if (and had (not= had tag))
              nil                                    # symbol and number at once
              [(st (st-s state) (st-c state) (st-d state)
                   [[w tag] (st-types state)]
                   (st-absent state)) nil]))
        (type-holds? tag w) [state nil]
        nil))))

(defn symbolo
  ``The goal that `x` is a symbol.

  In Janet both symbols and keywords are interned atoms and both are used as
  atoms in relations, so both satisfy this demand. Like `=/=`, the demand is
  not decided on the spot: if `x` is still unbound the demand is recorded and
  fires when `x` finally gets a value.``
  [x]
  (typeo :symbol x))

(defn numbero
  "The goal that `x` is a number, recorded and deferred like `symbolo`."
  [x]
  (typeo :number x))

(defn absento
  ``The goal that `tag` occurs nowhere inside `t`, at any depth.

  Stronger than `=/=`, which only forbids the whole terms from being equal:
  `absento` forbids the tag from appearing in any position, now or later.
  This is what a relational interpreter needs to say "this closure contains no
  such name anywhere inside it".``
  [tag t]
  (fn [state]
    (let [s (st-s state)
          r (push-absento tag t s)]
      (if (nil? r)
        nil
        (let [d2 (add-diseqs (st-d state) (r 1) s)]
          (if (= d2 FAIL)
            nil
            [(st s (st-c state) d2 (st-types state)
                 (array->chain (distinct (array/concat @[] (r 0)
                                                       (chain->array (st-absent state))))))
             nil]))))))

(def succeed
  "The goal that always succeeds, changing nothing."
  (fn [state] [state nil]))

(def fail
  "The goal that never succeeds."
  (fn [state] nil))

(defn call-fresh
  ``Call `f` with a fresh logic variable and run the goal it returns.
  `fresh` is the readable way to say this.``
  [f]
  (fn [state]
    ((f (mk-var (st-c state)))
     (st (st-s state) (+ 1 (st-c state)) (st-d state)
         (st-types state) (st-absent state)))))

(defn disj2 "Goal: `g1` or `g2`." [g1 g2] (fn [state] (mplus (g1 state) (fn [] (g2 state)))))
(defn conj2 "Goal: `g1` and `g2`." [g1 g2] (fn [state] (bind (g1 state) g2)))

# The macros below splice in the *values* of the helpers above rather than
# their names. A macro that expanded to the symbol `conj2` would only compile
# where that name happens to be visible — which depends on how the caller
# imported this module. Splicing the value works under any import alias.

(defn- fold-right
  ``Combine `xs` from the right: (f x1 (f x2 x3)).

  Right association is not a matter of taste here: with the interleaving
  merge, the way branches are nested decides the ORDER in which answers come
  out. Canonical miniKanren associates to the right, and answers of
  `(conde [a] [b] [c])` arrive as a, b, c. Folding left silently reorders
  them, which would make this implementation disagree with every published
  example while still looking correct.``
  [f xs]
  (var acc (last xs))
  (each x (reverse (slice xs 0 -2)) (set acc (f x acc)))
  acc)

(defn- conj-form
  "Build the form for: all of `goals` hold."
  [goals]
  # LEFT association, mirroring canon's bind*: (bind (bind (g0 st) g1) g2).
  # The SET of answers does not depend on this; the shape of the stream — and
  # with it the order and the cost of the search — does.
  (case (length goals)
    0 succeed
    1 (first goals)
    (do (var acc (first goals))
        (each g (slice goals 1) (set acc ~(,conj2 ,acc ,g)))
        acc)))

(defn- disj-form
  "Build the form for: at least one of `goals` holds."
  [goals]
  (case (length goals)
    0 fail
    1 (first goals)
    (fold-right (fn [g acc] ~(,disj2 ,g ,acc)) goals)))

(defn- mplus*-form
  ``Canon's mplus* chain over goal forms applied to state `st`: the first
  branch runs now, every further branch waits behind one thunk of its own.``
  [goals st]
  (var acc ~(,(last goals) ,st))
  (each g (reverse (slice goals 0 -2))
    (set acc ~(,mplus (,g ,st) (fn [] ,acc))))
  acc)

(defn- delay-form
  ``Build the form that postpones a goal until the search reaches it.

  Without this, a relation that mentions itself would be built forever before
  it ever ran. Postponing turns that into a stream that yields answers as it
  goes — the reason an infinite relation can be written down at all.``
  [g]
  (with-syms [st]
    ~(fn [,st] (fn [] (,g ,st)))))

(defmacro conj
  "Goal: all of `goals` hold. With no goals, succeeds."
  [& goals]
  (conj-form goals))

(defmacro disj
  "Goal: at least one of `goals` holds. With no goals, fails."
  [& goals]
  (disj-form goals))

(defmacro fresh
  ``Introduce logic variables and state the goals that must hold of them:

      (fresh [a d]
        (== l (cons* a d))
        (appendo d s res))``
  [bindings & goals]
  (var body (conj-form goals))
  (each name (reverse bindings)
    (set body ~(,call-fresh (fn [,name] ,body))))
  # Canon shape: the whole body sits behind ONE suspension. Every `fresh` is a
  # point where the search may pause, which is what keeps recursive relations
  # productive at the same granularity as the canon.
  (with-syms [st]
    ~(fn [,st] (fn [] (,body ,st)))))

(defmacro conde
  ``Branches. Every branch is tried and the answers of all branches are
  interleaved, so no branch can starve the others:

      (conde
        [(== l NIL) (== s out)]
        [(fresh [a d] ...)])``
  [& clauses]
  # Canon shape: ONE suspension around the whole branching point, then the
  # mplus* chain — first branch immediate, each further branch behind its own
  # thunk.
  (def conjs (map (fn [clause] (conj-form clause)) clauses))
  (case (length conjs)
    0 fail
    (with-syms [st]
      ~(fn [,st] (fn [] ,(mplus*-form conjs st))))))

### ── Reading answers back ───────────────────────────────────────────────────

(defn- reify-names [v s names]
  # Name the still-unbound variables in order of appearance: _.0, _.1, ...
  (cond
    (var? v) (if (in names v) names
               (put names v (symbol "_." (length names))))
    (pair? v) (reify-names (v 2) s (reify-names (v 1) s names))
    (indexed? v) (do (each x v (reify-names x s names)) names)
    names))

(defn- reify-apply [v names]
  (cond
    (var? v) (in names v)
    (pair? v) (cons* (reify-apply (v 1) names) (reify-apply (v 2) names))
    (tuple? v) (tuple ;(map (fn [x] (reify-apply x names)) v))
    (array? v) (array ;(map (fn [x] (reify-apply x names)) v))
    v))

(defn- visible?
  ``True if term `t` is observable in the answer: either not a variable at all,
  or a variable that got a name in the answer.``
  [t names s]
  (let [t (walk t s)]
    (if (var? t) (not (nil? (in names t))) true)))

(defn- all-visible?
  "True if every variable inside term `t` is named in the answer."
  [t names s]
  (let [t (walk t s)]
    (cond
      (var? t) (not (nil? (in names t)))
      (pair? t) (and (all-visible? (t 1) names s) (all-visible? (t 2) names s))
      (indexed? t) (all (fn [x] (all-visible? x names s)) t)
      true)))

(defn reify
  ``Read the answer for `v` out of `state`.

  Variables that are still unbound are shown as `_.0`, `_.1`, … — the answer
  says "anything may stand here", which is a real answer and not a failure.

  Surviving prohibitions are shown with the answer, because without them the
  answer would overstate what it knows: `_.0` alone claims "anything", while
  `(_.0 (=/= (_.0 5)))` claims "anything except 5".

  A prohibition is dropped WHOLE as soon as any one of its terms is invisible
  in the answer, and this is stricter than dropping the offending pair. A
  prohibition forbids a CONJUNCTION: "not (q = 5 and x = 3)". If `x` is a fresh
  variable nothing else constrains, some value of `x` always falsifies the
  conjunction, so the prohibition restricts nothing observable and must vanish
  entirely. Keeping the visible half would print `(=/= (_.0 5))` — a claim that
  `q` cannot be 5, which is simply false.``
  [v state]
  (let [s (st-s state)
        val (walk* v s)
        names (reify-names val s @{})
        shown (reify-apply val names)
        # Every standing constraint that touches something visible has to be
        # shown, for the same reason: bare `_.0` claims "anything", while a
        # pending `symbolo` means "any symbol" and a pending `absento` means
        # "anything not containing :x". An answer that hides them lies by
        # omission, and that is the one kind of lie a relational answer must
        # not tell.
        by-print (fn [a b] (< (string/format "%j" a) (string/format "%j" b)))
        # Which variables are known to be atoms. A `symbolo` or `numbero`
        # demand settles the SHAPE of a variable even while its value is
        # unknown, and that is what lets an `absento` on it be said more
        # plainly below.
        typed (let [m @{}]
                (each [v tag] (chain->array (st-types state)) (put m (walk v s) tag))
                m)
        # `absento` demands that have become ordinary prohibitions.
        #
        # 🔴 Once a variable is known to be an atom, "the tag is nowhere
        # inside it" and "it is not the tag" say the same thing — an atom has
        # no inside. The canon folds these (`absento-rhs-atomic?`), and the
        # difference is not cosmetic: on the quine it is one pair against a
        # line restating the whole lambda. And if the tag is COMPOUND while
        # the variable is an atom, the demand is satisfied outright — a
        # compound term does not fit inside an atom — so it vanishes rather
        # than being printed as a restriction that restricts nothing.
        # Shaped exactly like an entry of the prohibition store: a CHAIN of
        # one pair, variable first — that is the order `reify` prints and the
        # order `verify-constraints` reads.
        folded (seq [[tag t] :in (chain->array (st-absent state))
                     :let [tv (walk t s)]
                     :when (and (var? tv) (in typed tv) (leaf-tag? tag))]
                 [[tv tag] []])
        absent-pairs (sorted
                       (distinct
                         (seq [[tag t] :in (chain->array (st-absent state))
                               :let [tv (walk t s)]
                               # Both sides are walked and reified, and both
                               # must be fully visible: a tag is not always an
                               # atom, and splicing it raw once printed the
                               # engine's internals (`(:kanja/var 1)`).
                               :when (and (all-visible? tag names s)
                                          (all-visible? t names s)
                                          (not (and (var? tv) (in typed tv))))]
                           [(reify-apply (walk* tag s) names)
                            (reify-apply (walk* t s) names)]))
                       by-print)
        # One `absento` node holding every surviving demand, as the canon
        # prints it — for the same reason the prohibitions are gathered above.
        absents (if (empty? absent-pairs) @[] @[~(absento ,;absent-pairs)])
        # Every prohibition under ONE `=/=` node, each one a list of pairs —
        # the canon's shape. Printing them as separate nodes said the same
        # thing in a form its own test suites do not recognise.
        diseq-sets (sorted
                     (seq [c :in (array/concat @[] (chain->array (st-d state)) folded)
                           :when (all (fn [[k vv]] (and (visible? k names s)
                                                        (visible? vv names s)))
                                      (chain->array c))]
                       # A TUPLE, not an array: only a tuple hashes by value,
                       # and without that `distinct` below cannot tell one
                       # prohibition stated twice from two prohibitions.
                       (tuple ;(sorted (distinct (seq [[k vv] :in (chain->array c)]
                                                   [(reify-apply (walk* k s) names)
                                                    (reify-apply (walk* vv s) names)]))
                                       by-print)))
                     by-print)
        diseqs (if (empty? diseq-sets) @[] @[~(=/= ,;(distinct diseq-sets))])
        types (seq [[v tag] :in (chain->array (st-types state))
                    :when (visible? v names s)]
                [(symbol (type-name tag)) (reify-apply (walk* v s) names)])
        # Deterministic order matters: an answer that prints its constraints
        # in whatever order the stores happen to hold them is not comparable
        # between runs. `string` on a tuple does NOT give its printed form —
        # sorting by it silently did nothing, and passed only while the store
        # order happened to match.
        # The same demand can be stored twice — the answer must not say it
        # twice, or it reads as two different facts.
        cs (distinct (array/concat @[] diseqs types absents))]
    (if (empty? cs) shown [shown ;(sorted cs by-print)])))

(defn take-answers
  ``Take up to `n` answers from stream `strm`; `n` of nil means all of them,
  which only terminates if the relation has finitely many answers.``
  [n strm]
  (def out @[])
  (var strm strm)
  (while (and (or (nil? n) (< (length out) n))
              (do (set strm (pull strm)) strm))
    (array/push out (strm 0))
    (set strm (strm 1)))
  out)

(defn call-run
  "The function behind `run`; `run` is the readable way to call it."
  [n goal-fn]
  (let [q (mk-var 0)
        strm ((goal-fn q) (st EMPTY-S 1 [] [] []))]
    (map (fn [state] (reify q state)) (take-answers n strm))))

(defn- run-form
  ``Build the call behind `run` and `run*`.

  With one query variable the goals are asked about it directly. With several,
  the canon's shape is used: a hidden query variable is unified with the LIST
  of them, so every answer is a list of their values, in the order written.

      (run* [a b] (== a 1) (== b 2))   =>  @[(1 2)]

  Asking about several variables is not a convenience — running a relation
  usually means asking about a tuple of things at once, and writing that by
  hand costs a `fresh`, a `==` and a `llist` at every call site. Before
  02.08.2026 the extra names were silently dropped by the macro and the goals
  mentioning them failed to compile with `unknown symbol x` — an error that
  says nothing about the actual cause.``
  [n bindings goals]
  (if (<= (length bindings) 1)
    ~(,call-run ,n (fn [,(first bindings)] ,(conj-form goals)))
    (with-syms [q st]
      (var body (conj-form [~(,== ,q (,llist ,;bindings)) ;goals]))
      (each name (reverse bindings)
        (set body ~(,call-fresh (fn [,name] ,body))))
      # Same shape as `fresh`: the whole body behind ONE suspension.
      ~(,call-run ,n (fn [,q] (fn [,st] (fn [] (,body ,st))))))))

(defmacro run
  ``Ask for at most `n` answers:

      (run 5 [q] (appendo (llist 1 2) q (llist 1 2 3 4)))
      (run 3 [a b] (appendo a b (llist 1 2 3)))``
  [n bindings & goals]
  (run-form n bindings goals))

### ── Showing answers to a person ───────────────────────────────────────────

(defn- quoted
  ``If `v` is exactly the two-element list `(quote X)`, hand back X, else nil.

  For printing only. Every Lisp since 1960 writes that form as `'X`, and a
  generated program is read by a person far more often than it is diffed
  against a canon: the quine carries four `quote`s and nearly doubles in
  width without the shorthand.``
  [v]
  (when (and (pair? v) (= 'quote (v 1)) (pair? (v 2)) (= NIL ((v 2) 2)))
    ((v 2) 1)))

(defn show
  ``Render an answer the way a person reads it: `(1 2 3)` for a list,
  `(1 2 . _.0)` when the tail is still unknown, `'x` for `(quote x)`, and
  constraints kept beside the value they constrain.

  Printing the internal shape instead — `(:kanja/pair 3 (:kanja/pair 4
  :kanja/nil))` — is not merely ugly. An answer nobody can read is an answer
  nobody can check, and an engine whose output must be decoded by its author
  is back to being trusted rather than verified.

  ⚠️ The `'x` shorthand is OURS, not the canon's: faster-minikanren prints
  `(quote x)` in full. A deliberate step away from the canon towards the
  reader, and it lives in printing alone — the engine, the tests and
  `to-array` know nothing about it.``
  [x]
  (defn go [v]
    (cond
      (= NIL v) "()"
      (pair? v)
        (if-let [inner (quoted v)]
          (string "'" (go inner))
          (do (def parts @[])
            (var cur v)
            (while (pair? cur) (array/push parts (go (cur 1))) (set cur (cur 2)))
            (if (= NIL cur)
              (string "(" (string/join parts " ") ")")
              (string "(" (string/join parts " ") " . " (go cur) ")"))))
      (tuple? v) (string "(" (string/join (map go v) " ") ")")
      (array? v) (string "[" (string/join (map go v) " ") "]")
      (symbol? v) (string v)
      (string/format "%j" v)))
  (go x))

(defn show-all
  "Render a whole list of answers, one per line, numbered."
  [answers]
  (if (empty? answers)
    "  (no answers)"
    (string/join
      (seq [[i a] :pairs answers] (string/format "  %d. %s" (+ 1 i) (show a)))
      "\n")))

### ── Resumable search ──────────────────────────────────────────────────────
###
### A search does not have to be run to the end. The answer stream IS the state
### of the search: holding on to it and pulling again later continues exactly
### where the previous take stopped, without redoing anything.
###
### 🔴 A correction to an earlier design note. This resumability comes from the
### stream being an ordinary value, NOT from Janet fibers — no coroutine is
### involved. And Janet 1.41 has no instruction-count limit for fibers
### (`fiber/setmaxfuel` does not exist), so the step budget below is our own
### counter, not a runtime facility. Both claims were assumed before they were
### checked; they are written down here in their corrected form.

(defn search
  ``Begin a search without running it. Returns a handle that answers can be
  taken from, repeatedly, at any later time.``
  [goal-fn]
  (let [q (mk-var 0)]
    @{:var q
      :stream ((goal-fn q) (st EMPTY-S 1 [] [] []))
      :taken 0
      :steps 0
      :unifications 0
      :exhausted false
      :error nil}))

(defn search-stats
  ``What this search has cost so far and where it stands.

  Not decoration: with a complete interleaving search the only way to tell
  "thinking hard" from "stuck in one call" is to watch whether the work
  counters move. That distinction cost two days to learn the hard way, so the
  numbers are part of the interface rather than something to bolt on when
  something goes wrong.``
  [srch]
  @{:answers (srch :taken)
    :steps (srch :steps)
    :unifications (srch :unifications)
    :exhausted (srch :exhausted)
    :error (srch :error)})

(defn search-failed?
  "True if a relation raised an error during this search."
  [srch]
  (not (nil? (srch :error))))

(defn search-exhausted?
  ``True if this search has been looked at and had nothing more to give.

  Taking the last answer does not set this: having taken six answers out of
  six, nobody yet knows that a seventh does not exist. Exhaustion is a
  DISCOVERY, made by one more look that comes back empty. Claiming it earlier
  would mean looking ahead — doing work nobody asked for, and losing the
  property that a take costs only what it yields.``
  [srch]
  (srch :exhausted))

(defn take-more!
  ``Take up to `n` more answers from a search, continuing where the last take
  stopped. With `max-steps`, stop after that many stream forcings and return
  what was found so far — the search stays resumable and is NOT lost.

  Returns @{:answers [...] :stopped-early bool :steps int}. `:stopped-early`
  distinguishes "the budget ran out" from "there are no more answers", which
  are different facts and must not share a shape.``
  [srch n &opt max-steps]
  (def out @[])
  (var steps 0)
  (var early false)
  (var failure (srch :error))
  (def u0 UNIFS)
  (var strm (srch :stream))
  # A relation is ordinary Janet code and may raise. If it does, the error is
  # caught here — but it is NOT swallowed and the branch is NOT skipped.
  # Skipping would make a broken relation indistinguishable from one with no
  # answers, which is the single worst thing a search can do. The error is
  # attached to the search, the search is marked dead, and every later take
  # returns the same error instead of an innocent empty result.
  (when (nil? failure)
    (try
      (while (and (< (length out) n) (not early) (not (nil? strm)))
        (while (and (function? strm) (not early))
          (if (and max-steps (>= steps max-steps))
            (set early true)
            (do (set strm (strm)) (++ steps))))
        (when (and (not early) (not (nil? strm)))
          (array/push out (reify (srch :var) (strm 0)))
          (set strm (strm 1))))
      ([e] (set failure e) (set strm nil))))
  (put srch :error failure)
  (unless failure (put srch :stream strm))
  (put srch :taken (+ (srch :taken) (length out)))
  (put srch :steps (+ (srch :steps) steps))
  (put srch :unifications (+ (srch :unifications) (- UNIFS u0)))
  (put srch :exhausted (and (nil? failure) (nil? strm) (not early)))
  @{:answers out :stopped-early early :steps steps :error failure})

(defmacro run*
  ``Ask for every answer. Terminates only if there are finitely many —
  with an infinite relation, use `run`. Takes several query variables just as
  `run` does.``
  [bindings & goals]
  (run-form nil bindings goals))
