# A relational interpreter for a tiny Lisp.
#
# This is the demonstration that relational programming is not a curiosity.
# The interpreter is written once, as a RELATION between an expression, an
# environment and a value. Nothing in it decides which of the three is input.
# So the same definition answers:
#
#   · "what does this program evaluate to?"          (the ordinary direction)
#   · "which program evaluates to this?"             (program synthesis)
#   · "which program evaluates to ITSELF?"           (a quine — generated,
#                                                     not checked)
#
# Following Byrd, Holk and Friedman, "miniKanren, Live and Untagged: Quine
# Generation via Relational Interpreters" (Scheme Workshop 2012). The tagless
# representation is what makes the third question answerable: closures are
# ordinary data, and `absento` keeps user programs from forging one.
#
# The language: quote · variable reference · lambda of one argument ·
# application · list.

(import ../kanja :as k)

(defn not-in-envo
  "Name `x` is not bound anywhere in environment `env`."
  [x env]
  (k/conde
    [(k/== k/NIL env)]
    [(k/fresh [y v rest]
       (k/== (k/llist* (k/cons* y v) rest) env)
       (k/=/= y x)
       (not-in-envo x rest))]))

(defn lookupo
  "Name `x` is bound to `t` in `env` — the first binding wins."
  [x env t]
  (k/fresh [y v rest]
    (k/== (k/llist* (k/cons* y v) rest) env)
    (k/conde
      [(k/== y x) (k/== v t)]
      [(k/=/= y x) (lookupo x rest t)])))

# eval-expo and proper-listo are mutually recursive: a `list` form evaluates
# its elements, and each element is an arbitrary expression.
(var eval-expo nil)

(defn proper-listo
  "Every element of `exp` evaluates, under `env`, to the matching element of `val`."
  [exp env val]
  (k/conde
    [(k/== k/NIL exp) (k/== k/NIL val)]
    [(k/fresh [a d t-a t-d]
       (k/== (k/cons* a d) exp)
       (k/== (k/cons* t-a t-d) val)
       (eval-expo a env t-a)
       (proper-listo d env t-d))]))

(set eval-expo
  (fn eval-expo [exp env val]
    (k/conde
      # (quote v) — v is the value, provided the program did not rebind `quote`
      # and provided v is not a forged closure.
      [(k/fresh [v]
         (k/== (k/llist 'quote v) exp)
         (k/absento 'closure v)
         (not-in-envo 'quote env)
         (k/== v val))]

      # (list e ...) — evaluate each element
      [(k/fresh [args]
         (k/== (k/cons* 'list args) exp)
         (k/absento 'closure args)
         (not-in-envo 'list env)
         (proper-listo args env val))]

      # a variable
      [(k/symbolo exp) (lookupo exp env val)]

      # application: (rator rand)
      [(k/fresh [rator rand x body env2 a]
         (k/== (k/llist rator rand) exp)
         (eval-expo rator env (k/llist 'closure x body env2))
         (eval-expo rand env a)
         (eval-expo body (k/llist* (k/cons* x a) env2) val))]

      # (lambda (x) body) — the value is a closure, which is ordinary data
      [(k/fresh [x body]
         (k/== (k/llist 'lambda (k/llist x) body) exp)
         (k/symbolo x)
         (not-in-envo 'lambda env)
         (k/== (k/llist 'closure x body env) val))])))

(defn evalo
  "Program `exp` evaluates to `val` in the empty environment."
  [exp val]
  (eval-expo exp k/NIL val))

(defn show
  ``Render an answer the way a person reads it — `(lambda (_.0) ...)`, not
  `@[@[lambda @[_.0] ...]]`.

  This used to hand back `k/to-array`, which is the right function for giving
  an answer to ordinary Janet code and the wrong one for showing it to a
  human: it prints the engine's own shape. `k/show` says so in its own
  docstring — "an answer nobody can read is an answer nobody can check" — and
  the quine demo, the one thing anyone is shown first, broke that rule.
  Use `to-data` below when the answer is going to code rather than to eyes.``
  [x]
  (k/show x))

(defn to-data
  "Hand an answer back to ordinary Janet code as arrays and tuples."
  [x]
  (k/to-array x))
