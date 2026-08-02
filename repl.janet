# A REPL for kanja. Answers are printed the way a person reads them, not the
# way the engine stores them.
(import ./kanja :prefix "")
(import ./kanja/relations :prefix "")
(import ./examples/interpreter :prefix "")


### The colours were LIFTED from the editor pane next door (nvim, tokyonight-moon)
### with `tmux capture-pane -e`, not picked by eye: text 200;211;245 · mauve
### 192;153;255 · cyan 134;225;252 · green 195;232;141 · muted 99;109;166 ·
### dark 59;66;97. The terminal advertises RGB (checked with
### `tmux show -gs terminal-features` and by printing), so truecolor is used
### rather than a 256-colour approximation.
(def- C @{:name   "\e[1m\e[38;2;134;225;252m"
          :text   "\e[38;2;200;211;245m"
          :dim    "\e[38;2;122;133;190m"
          :rule   "\e[38;2;84;92;126m"
          :code   "\e[38;2;134;225;252m"
          :accent "\e[1m\e[38;2;200;211;245m"
          :off    "\e[0m"})

(defn- c [k s] (string (C k) s (C :off)))

(defn help []
  # The sheet is coloured by MEANING, not by taste: the forms a person will
  # TYPE are cyan (the colour code has in the pane next door), the prose about
  # them is quieter, and the rules are darkest — they hold the frame without
  # arguing with the text.
  (print (string "\n  " (C :rule) "── " (C :off) (c :name "kanja")
                 (c :rule " · cheat sheet ─────────────────────────────────────────────")))
  (print (string "  " (c :accent "▸ LISTS FOR RELATIONS ARE BUILT WITH (llist 1 2 3), NOT [1 2 3].")))
  (print (c :dim `     A native Janet tuple has a fixed length and cannot say "and after this,
     something not yet known" — so relations carry their own lists. Hand a
     relation a tuple and it answers NOTHING, and nothing here means "no
     solutions": indistinguishable from a real answer. Everyone's first
     mistake. No longer yours.`))
  (print "")
  (each [form note] [["(run* [q] (== q 5))" "ask for everything"]
                     ["(run 3 [q] ...)" "ask for the first three"]
                     ["(run* [a b] ...)" "ask about several at once"]
                     ["(llist 1 2 3)" "a list · (llist* 1 2 tail) — unknown tail"]
                     ["(== a b)" `"these two are the same thing"`]
                     ["(=/= a b) (symbolo x) (numbero x)" "demands"]
                     ["(absento :tag x)" "the tag is nowhere inside, at any depth"]
                     ["" "  the tag may be compound: (absento (llist 1 2) x)"]
                     ["(conde [goal ...] [goal ...])" "a fork · (fresh [a b] ...) — new holes"]
                     ["(appendo l s out) (membero x l)" "relations that ship with it"]
                     ["(evalo prog value)" "the relational interpreter"]
                     ["(search f) (take-more! s n [budget])" "a search you can put down and resume"]
                     ["(examples) · (example 3)" "ready to run — nothing to paste"]
                     ["(help)" "this sheet"]]
    (printf "  %s%s%s%s" (C :code) form (C :off)
            (string (string/repeat " " (max 1 (- 37 (length form)))) (c :dim note))))
  (print (c :rule "  ────────────────────────────────────────────────────────────────────────\n")))

### The examples live HERE rather than in your clipboard, on purpose: Janet's
### line editor stumbles on pasted text, leaving a fragment behind and then
### complaining about the wreckage. Rather than fix someone else's editor, we
### remove the need to paste at all.

(def- EXAMPLES
  @[["join two lists — the ordinary question"
     '(run* [q] (appendo (llist 1 2) (llist 3 4) q))]
    ["the same rule BACKWARDS: what was appended to the second"
     '(run* [q] (appendo (llist 1 2) q (llist 1 2 3 4)))]
    ["and sideways: EVERY pair that joins into (1 2 3)"
     '(run* [x y] (appendo x y (llist 1 2 3)))]
    ["holes: what the machine cannot know, it names a hole"
     '(run 4 [q] (fresh [x y] (appendo x y q)))]
    ["membership runs both ways"
     '(run* [q] (membero q (llist :bread :salt :water)))]
    ["a demand lives on in time: anything but five"
     '(run* [q] (=/= q 5))]
    ["and fires later — so there are no answers"
     '(run* [q] (=/= q 5) (== q 5))]
    ["absento looks at any depth"
     '(run* [q] (absento :poison q))]
    ["the interpreter BACKWARDS: compose programs yielding :treasure"
     '(run 3 [q] (evalo q :treasure))]
    ["🔴 QUINE: a program that evaluates to itself"
     '(run 1 [q] (evalo q q))]])

(defn examples
  "List the examples. Run the Nth one with (example N)."
  []
  (print "")
  (each [i [caption _]] (pairs EXAMPLES)
    (printf "  %2d. %s" (+ 1 i) caption))
  (print "\n  run one:  (example 3)\n"))

(defn example
  "Show and run the Nth example — nothing needs to be typed by hand."
  [n]
  (if-let [[caption form] (get EXAMPLES (- n 1))]
    (do (printf "\n  %s\n  %j\n" caption form)
        (def value (eval form))
        (if (array? value) (print (show-all value)) (pp value))
        (print ""))
    (printf "  no such example; there are %d — type (examples)" (length EXAMPLES))))

(defn- render [x]
  # `run` and `run*` hand back an ARRAY of answers — that is what gets printed
  # readably. The rule is deliberately blunt: guessing "does this look like an
  # answer" already got it wrong once on a bare hole `_.0`, and fragile
  # recognition is worse than a plain rule.
  # `(examples)` and `(example N)` print by themselves and return nil — that
  # nil is not shown: in a teaching REPL it reads as "something went wrong".
  (cond
    (array? x) (print (show-all x))
    (nil? x) nil
    (pp x)))

# One line, in the tone of Janet's own banner. Note that Janet's line is NOT
# printed here: this file calls `repl` itself and so bypasses the standard
# entry point along with its banner. That is why the door has to be named —
# without it a newcomer has no way to learn that `(help)` exists at all.
# The version sits directly against the name it belongs to; anywhere else it
# reads as the version of Janet.
# "ask", not "for help": in this library nothing is called and nothing returns.
# Questions are asked and answers come back — including this one.
(print (string "\n  " (c :name "kanja") " " (c :dim version)
               (c :rule " · ") (c :text "miniKanren for Janet")
               (c :rule " · ") (c :code "(help)") "\n"))
(repl nil (fn [f x] (if (= :dead (fiber/status f)) (render x) (debug/stacktrace f x))) (curenv))
