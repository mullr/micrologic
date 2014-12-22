(ns micro-logic.core
  (:require [micro-logic.protocols :refer :all]))

;; ## Common variables
;; - *c* The id of an lvar
;; - *s* A substitution map. Keys are lvars, values are either lvars or values.
;; - *u, v* Either an lvar or a literal value. Unification terms, more precisely.
;; - *g* A goal function. Given a substition map, produce a stream of substitution maps.
;; - *gc* Goal constructor function.
;; - *$* A stream: either a function, an lcons, or nil.
;; - *st* A state: holds a substitution map and the id of the next unallocated lvar.

;; ## Logic Variables
;;
;; Logic variables (lvars for short) are the unknown items that will
;; be given a value by the unifier. Each of them has an id (*c*); this
;; is a number which is assigned when a new variable is allocated by
;; (fresh). The interpreter state stores the next id to use.
(defrecord LVar [c])
(defn lvar [c] (LVar. c))
(defn lvar? [x] (instance? LVar x))


;; ## Substitutions and Walking
;;
;; A substitution map (*s*) gives mappings from logic variables to
;; their values.
;;
;; To see what value an lvar is bound to in a given substitution map,
;; use `(walk u s)`. (*u* is an lvar or a value) Supposing *a* and *b*
;; are lvars; in this simple case, `(walk a {a 1})` returns `1`.
;;
;; Minikanren derivatives (including this one) use *triangular*
;; substitutions, which means that an lvar may map to another lvar.
;; Walk will follow these variable references until a value is
;; reached. For example, `(walk a {a b, b 2})` returns `2`.
;;
;; The observant reader may note that it is easy to construct a
;; substitution map with a loop in it: `(walk a {a b, b a})` will not
;; terminate. This case may be handled (but is not, in this
;; implementation) with an *occurs-check* function call when adding
;; new substitutions.
;;
;; We implement this in clojure with the IWalk protocol, since it is
;; polymorphic on the type of *u*.
;;
;; Note: when walking for a variable, it may not be present in the
;; substitution map.  In this case, the variable itself is returned,
;; indicating that the variable is currently unbound.
(extend-protocol IWalk
  LVar
  (walk [u s] (if-let [val (get s u)]
                (recur val s)
                u))
  Object
  (walk [u s] u)

  nil
  (walk [u s] nil))

;; # Unification

(defn unify
  "Given two terms *u* and *v*, and an existing substitution map *s*,
  unify produces a new substitution map with mappings that will make u
  and v equal."
  [u v s]
  (let [u (walk u s),  v (walk v s)
        ulv (lvar? u), vlv (lvar? v)]
    (cond
      (and ulv vlv (= u v)) s
      ulv (assoc s u v)
      vlv (assoc s v u)
      (= u v) s
      :default (unify-terms u v s))))

;; This unifier is extensible, in the spirit of core.logic. Only
;; unification on basic types is directly implemented here. By
;; extending the IUnifyTerms protocol, special unification logic may
;; be supplied for any data type.
;;
;; A *term* is, somewhat circularly, something you can pass to the unifier.
;; this includes lvars, regular values, and values of any type to which
;; you have extended IUnifyTerms.
(extend-protocol IUnifyTerms
  Object
  (unify-terms [u v s]
    (if (= u v) s)))



;; # Streams
;;
;; The lazy stream mechanism is one of the really interesting parts
;; about miniKanren. It's different from regular scheme linked lists
;; or even clojure's lazy sequences - it lets you schedule work fairly
;; between different branches of the search space, each of which is
;; represented by a stream.
;;
;; Unlike a clojure seq, a stream may be in one of three states:
;;
;; - mature (head realized)
;; - immature (head unrealized)
;; - empty
;;
;; The immature state indicates that there is some work to be done to
;; either compute the head of the stream or to determine if it's
;; empty.  Contrast this with clojure lazy sequences, where the act of
;; getting the rest of a sequence is what triggers computation. This
;; difference is subtle but important, and it allows the interleaved
;; scheduling to work.
;;
;; ### Things you can do with a stream
;; - Merge two of them together with `merge-streams`
;; - Map a function over it with `mapcat-stream`, as long as that
;;   function itself produces streams.
;; - Realize its head with `realize-stream-head`. This will transition it
;;   to either immature or empty, performing any necessary work
;;   along the way.
(def empty-stream
  (reify IStream
    (merge-streams [$1 $2] $2)
    (mapcat-stream [$ g] $)
    (realize-stream-head [$] $)))

;; ### Mature streams (StreamNode)
;;
;; A head-realized streams is represented by an instance of StreamNode.
;; This is kind of like a linked list: `head` is the realized value that
;; can be taken from the stream, and `next` is the stream which follows.
;; But these streams are polymorphic; `next` isn't necessarily a StreamNode,
;; just some other thing which extends the IStream protocol.
;;
;; Note that, if we have only StreamNodes (i.e. fully realized
;; streams), merge-streams is equivalent to `concat` and
;; `mapcat-stream` to `mapcat`.
(deftype StreamNode [head next]
  IStream
  (merge-streams [$1 $2] (StreamNode. head
                                      (merge-streams next $2)))
  (mapcat-stream [$ g] (merge-streams (g head)
                                      (mapcat-stream next g)))
  (realize-stream-head [$] $))

;; ### Immature streams (IFn)
;;
;; An immature (head-unrealized) stream is represented by a thunk (a
;; function of no arguments).
;;
;; Executing the thunk does one unit of work and yields back a stream. This may
;; in turn be a function, so you might have to keep calling the returned function
;; many times until you get down to a realized value. This is exactly what
;; `realize-stream-head` does here, by way of `trampoline`.
;;
;; #### Merging
;; Merging is the tricky part - this is what makes the search
;; interleaving. Let's examine the definition:
;;
;;     clojure.lang.IFn
;;     (merge-streams [$1 $2] #(merge-streams $2 ($1)))
;;
;; Working from the inside out: we know that $1 is a function because
;; we're extending IStream onto IFn; calling it will perform one 'step
;; of computation', whatever that might be. It returns a stream.
;; Then we merge that stream with $2, the second parameter of this merge operation,
;; *but the order is reversed*.
;;
;; Finally, the above operation is all wrapped in a thunk. So we end up with a
;; function that:
;;
;; - performs the work for the first thing you constructed it with
;; - returns a new stream, putting the second thing you constructed it
;;   with at the head.
;;
;; An imaginary repl session may make this clearer:
;;
;;     > (def a #(stream (+ 1 1)))
;;     > (def b #(stream (+ 10 20))
;;     > (def s (merge-streams a b))
;;     #(merge-streams #(stream (+ 10 20) (#(stream (+ 1 1))))
;;
;;     > (def s' (s))
;;     #(merge-streams (stream 2) (#(stream (+ 10 20))))
;;
;;     > (def s'' (s'))
;;     (StreamNode. 2 (StreamNode. 30))
;;
;; #### Mapping
;; mapcat-stream is somewhat simpler.
;;
;;     clojure.lang.IFn
;;     (mapcat-stream [$ g] #(mapcat-stream ($) g))
;;
;; The basic concept here is pretty straightforward: make a new thunk which,
;; when executed later, will do some work and then mapcat `g` over the result.
;;
;; TODO: explain why this needs to be wrapped in a thunk
(extend-protocol IStream
  clojure.lang.IFn
  (merge-streams [$1 $2] #(merge-streams $2 ($1)))
  (mapcat-stream [$ g] #(mapcat-stream ($) g))
  (realize-stream-head [$] (trampoline $)))

(defn stream [s] (StreamNode. s empty-stream))

;; #### Seq conversion
;;
;; We of course like to deal with lazy sequences in clojure, and it's
;; fairly straightforward to convert it. Running realize-stream-head
;; bounces the trampoline until a result comes out, at which point we
;; can give it to the caller.
(defn stream-to-seq [$]
  (lazy-seq
   (let [$' (realize-stream-head $)]
     (if (= empty-stream $')
       '()
       (cons (.head $') (stream-to-seq (.next $')))))))


;; ## Goals

;; A *state* is a record containing a substitution map *s* and the id
;; of the next unbound logic variable *c*.
(defrecord State [s c])
(defn state [s c] (State. s c))
(def empty-state (state {} 0))

;; A goal is a function which, given a state, returns a stream of
;; states. Conceptually, it encodes some constraints. Give it an input
;; state, and it will give you one output state for each way it can
;; meet those constraints.

;; Rather than dealing with goals directly, we usually use
;; *goal constructors*; given some parameter (usually a unification term or
;; another goal), they will return a goal function which closes over
;; it.

;; ### Basic goal constructors

(defn ===
  "Given two terms u and v, create a goal that will unify them. The
  goal takes an existing state and returns either a state with
  bindings for lvars in u and v (using `unify`), or returns the empty
  stream if no such state exists. "
  [u v]
  (fn unify-goal [st]
    (if-let [s' (unify u v (.s st))]
      (stream (state s' (.c st)))
      empty-stream)))

(defn call-fresh
  "Wrap the goal constructor *gc*, a function of a single lvar, in a
  goal that allocates a new lvar from its state parameter and passes
  it to *gc*."
  [gc]
  (fn fresh-goal [st]
    (let [c (.c st)]
     ((gc (lvar c)) (state (.s st) (inc c))))))

(defn ldisj
  "Logical disjuction ('or'). Construct a new goal that succeeds
  whenever *g1* or *g2* succeed. `merge-streams` is used on each
  goal's output to ensure fair scheduling between the two."
  [g1 g2]
  (fn disj-goal [st]
    (merge-streams (g1 st) (g2 st))))

(defn lconj
  "Logical conjunction ('and'). Construct a new goal that succeeds
  when both *g1* and *g2* succeed."
  [g1 g2]
  (fn conj-goal [st]
    (mapcat-stream (g1 st) g2)))



;; ## Auxilliary macros
;;
;; At this point, we have defined everything we need to do logic
;; programming.  But it's very inconvenient; some utility macros make
;; the task more bearable.

(defmacro delay-goal
  "Wrap the given goal in a new one which, when executed, simply
  returns a thunk. Recall that goal functions return streams, and that
  a function is a valid kind of stream (an immature stream). The goal
  will finally be executed when the thunk is evaluated by
  realize-stream-head.

  This is useful for defining recursive goals."
  [g]
  `(fn delayed-goal-outer [st#]
     (fn delayed-goal-inner [] (~g st#))))

(defmacro ldisj+
  "Extended version of the `ldisj` function. This one handles multiple
  arguments, instead of just two. It also automatically wraps each goal
  with `delay-goal`, so you don't need to worry about adding them yourself.

  (This does have a performance cost, but speed is not the point of this port)"
  ([g] `(delay-goal ~g))
  ([g & gs] `(ldisj (delay-goal ~g) (ldisj+ ~@gs))))

(defmacro lconj+
  "Like `ldisj+`, but for `lconj`."
  ([g] `(delay-goal ~g))
  ([g & gs] `(lconj (delay-goal ~g) (lconj+ ~@gs))))


(defmacro conde
  "The regular miniKanren `conde` form, a disjunction of
  conjunctions. Supposing that *a* and *b* are lvars,

      (conde
        [(=== a 1) (=== b 2)]
        [(=== a 7) (=== b 12)})

  will produce two results: {a 1, b 2} and {a 7, b 12}."
  [& clauses]
  `(ldisj+ ~@(map (fn [clause]
                    `(lconj+ ~@clause))
                  clauses)))

(defmacro fresh
  "Provide a more convenient syntax for `call-fresh`. `fresh` lets you
  declare multiple logic variables and once, and it takes care of the
  function declaration mechanics for you.

  The body of fresh is passed to `lconj+`, a logical 'and'.

      (fresh [x y]
        (=== x 1)
        (=== y 2))

  Will give one result, {x 1, y 2}."
  [var-vec & clauses]
  (if (empty? var-vec)
    `(lconj+ ~@clauses)
    `(call-fresh (fn [~(first var-vec)]
                   (fresh [~@(rest var-vec)]
                     ~@clauses)))))


;; ## Reificiation

;; In miniKanren, reification refers to extracting the desired values
;; from the stream of states you get as a result of executing a goal.
(defn reify-name [n]
  (symbol (str "_." n)))

(defn reify-s [v s]
  (reify-s* (walk v s) s))


(extend-protocol IReifySubstitution
  LVar
  (reify-s* [v s] (let [n (reify-name (count s))]
                    (assoc s v n)))

  Object
  (reify-s* [v s] s))


(defn walk* [v s]
  (let [v' (walk v s)]
    (deep-walk v' s)))

(extend-protocol IDeepWalk
  LVar
  (deep-walk [v s] v)

  Object
  (deep-walk [v s] v))


(defn reify-state-first-var [st]
  (let [v (walk* (lvar 0) (.s st))]
    (walk* v (reify-s v {}))))

(defn reify-state-lvar [st lv]
  (let [v (walk* lv (.s st))]
    (walk* v (reify-s v {}))))


;;; run interface

(defn call-empty-state [g]
  (g empty-state))

(defmacro basic-run*
  "reify-fn: state -> thing you want"
  [reify-fn query-var-vec & gs]
  `(->> (fresh [~@query-var-vec] ~@gs)
     call-empty-state
     stream-to-seq
     (map ~reify-fn)))

(defmacro run* [query-var-vec & gs]
  `(basic-run* reify-state-first-var [~@query-var-vec] ~@gs))

(defmacro run [n query-var-vec & gs]
  `(take ~n (run* ~query-var-vec ~@gs)))
