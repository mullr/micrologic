;; This is a logic programming system embedded in Clojure. It's made
;; of a few simple pieces, some surprising in their depth; we'll
;; examine them each in turn, then put them together and show how to
;; do some logic programming with the result.
;;
;; ## Audience
;;
;; This literate program is written for any Clojure programmer who
;; wants to know more about logic programming. You don't need a
;; particularly deep knowledge of logic programming going into this,
;; but it may help to have gone through a tutorial or two so you can
;; recognize the end when we get there.
;;
;; ## Overview
;;
;; We'll start by defining [*logic variables*](#lvars) (*lvars*) and
;; [*substition maps*](#substitutions). An lvar is a variable which
;; gets a value through an entry in the subsitution map. We then
;; define a [*walk*](#walk) function to get the value of an lvar out
;; of an existing substitution map.
;;
;; With those in place, we can define the [*unifier*](#unification), a
;; way to declare that two terms (which may include lvars) must be
;; equal and to compute what substitution map must be used to make
;; them equal.
;;
;; We then take a left turn into the most remarkable poart of
;; miniKanren, its definition of [*lazy streams*](#streams). These are
;; unordered streams that can be composed together in a fair way: no
;; one stream will monopolize all computing resources, instead
;; interleaving its computation and its results with other streams it
;; has been combined with.
;;
;; The above are the primitive elements; we can use them to start to
;; define the actual logic interpreter.  We begin with a definition of
;; [*interpreter state*](#goals), (which contains the current
;; substitution map and some other book-keeping information).
;;
;; Then we can create [*goal*](#goals) functions, which take a
;; prexisting interpreter state and return a stream of possible
;; interpreter states which meet the goal's constraints.  Several
;; useful *goal constructors* are defined: *===* (unify), *ldisj*
;; (logical or), *lconj* (logical and), *call-fresh* (call a function
;; with a newly allocated lvar) and some extended utilities.
;;
;; To translate streams of interpreter states (the output of each goal
;; function) to something more useful, we implement a
;; [*reify*](#reify) function that extract the desired information
;; from each state.
;;
;; Finally, we put the pieces together to define the
;; [programmer interface](#programmerInterface): the *run* and *run**
;; macros, *conde* and *fresh*, which will be familiar to any core.logic
;; or minikanren programmer.
;;
;; ### Extensibility
;;
;; We use Clojure's protocols in defining many of the above functions, in a bid
;; to make the core logic system extensible to new data structures. (this is
;; similar to core.logic) By way of example, and also to be able to do some
;; useful logic programming, extend the core to support sequences.
;;
;; First we have to define a custom linked-list type. Clojure doesn't
;; support 'improper lists', which are very useful for this
;; application.  We then extend the unifier and the reifier to support
;; this type and define the basic miniKanren sequence goals using it.
;; (*conso*, *firsto*, *resto*, *emptyo*)
;;
;; <hr>
(ns micro-logic.core
  (:require [micro-logic.protocols :refer :all]))


;; ## <a name="lvars"></a>Logic Variables
;;
;; Logic variables (lvars for short) are the unknown items that will
;; be given a value by the unifier. Each of them has an id; this
;; is a number which is assigned when a new variable is allocated.
(defrecord LVar [id])
(defn lvar [id] (LVar. id))
(defn lvar? [x] (instance? LVar x))


;; ## <a name="substitutions"></a><a name="walk"></a>Substitutions and Walking
;;
;; A substitution map (*s-map*) is a hash-map that gives
;; mappings from logic variables to their values.
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
  (walk [u s-map] (if-let [val (get s-map u)]
                    (recur val s-map)
                    u))
  Object
  (walk [u s-map] u)

  nil
  (walk [u s-map] nil))

;; ## <a name="unification"></a>Unification

(defn unify
  "Given two terms *u* and *v*, and an existing substitution map *s*,
  unify produces a new substitution map with mappings that will make u
  and v equal.

  This unifier is extensible, in the spirit of core.logic. Only
  unification on basic types is directly implemented here. By
  extending the IUnifyTerms protocol, special unification logic may be
  supplied for any data type.

  A *term* is, somewhat circularly, something you can pass to the
  unifier.  this includes lvars, regular values, and values of any
  type to which you have extended IUnifyTerms. "
  [u v s-map]
  (let [u (walk u s-map),    v (walk v s-map)
        u-is-lvar (lvar? u), v-is-lvar (lvar? v)]
    (cond
      ;; Unifying two lvars adds no information to the substitution map
      (and u-is-lvar v-is-lvar (= u v)) s-map

      ;; Unifying an lvar with some other value creates a new entry in
      ;; the substitution map
      u-is-lvar (assoc s-map u v)
      v-is-lvar (assoc s-map v u)

      ;; Unifying two non-lvars is delegated to the polymorphic
      ;; `unify-terms` function, from IUnifyTerms.
      :default (unify-terms u v s-map))))

;; If there is no more specific definition, unificiation between two
;; values should at least succeed if they are equal. Return nil if
;; they are not, indiciating that the terms cannot be unified.
(extend-protocol IUnifyTerms
  Object
  (unify-terms [u v s-map]
    (if (= u v) s-map))

  nil
  (unify-terms [u v s-map]
    (if (= u v) s-map)))



;; # <a name="streams"></a>Lazy Streams
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
    (merge-streams [stream-1 stream-2] stream-2)
    (mapcat-stream [stream g] stream)
    (realize-stream-head [stream] stream)))

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
  (merge-streams [stream-1 stream-2] (StreamNode. head
                                      (merge-streams next stream-2)))
  (mapcat-stream [stream g] (merge-streams (g head)
                                      (mapcat-stream next g)))
  (realize-stream-head [stream] stream))

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
;;     (merge-streams [stream-1 stream-2] #(merge-streams stream-2 (stream-1)))
;;
;; Working from the inside out: we know that stream-1 is a function because
;; we're extending IStream onto IFn; calling it will perform one 'step
;; of computation', whatever that might be. It returns a stream.
;; Then we merge that stream with stream-2, the second parameter of this merge operation,
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
;;     (mapcat-stream [stream g] #(mapcat-stream (stream) g))
;;
;; The basic concept here is pretty straightforward: make a new thunk which,
;; when executed later, will do some work and then mapcat `g` over the result.
;;
;; TODO: explain why this needs to be wrapped in a thunk
(extend-protocol IStream
  clojure.lang.IFn
  (merge-streams [stream-1 stream-2] #(merge-streams stream-2 (stream-1)))
  (mapcat-stream [stream g] #(mapcat-stream (stream) g))
  (realize-stream-head [stream] (trampoline stream)))

(defn make-stream [s] (StreamNode. s empty-stream))

;; #### Seq conversion
;;
;; We of course like to deal with lazy sequences in clojure, and it's
;; fairly straightforward to convert it. Running realize-stream-head
;; bounces the trampoline until a result comes out, at which point we
;; can give it to the caller.
(defn stream-to-seq [stream]
  (lazy-seq
   (let [stream (realize-stream-head stream)]
     (if (= empty-stream stream)
       '()
       (cons (.head stream) (stream-to-seq (.next stream)))))))


;; ## <a name="goals"></a>Goals

;; A *state* is a record containing a substitution map *s* and the id
;; of the next unbound *next-id*.
(defrecord State [s-map next-id])
(defn make-state [s-map next-id] (State. s-map next-id))
(def empty-state (make-state {} 0))
(defn with-s-map [state s-map] (assoc state :s-map s-map))
(defn with-next-id [state next-id] (assoc state :next-id next-id))

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
  bindings for the lvars in u and v (using `unify`), or returns the empty
  stream if no such state exists. "
  [u v]
  (fn unify-goal [{:keys [s-map] :as state}]
    (if-let [s-map' (unify u v s-map)]
      (make-stream (with-s-map state s-map'))
      empty-stream)))

(defn call-fresh
  "Wrap *goal-custructor*, a function of a single lvar, in a
  goal that allocates a new lvar from its state parameter and passes
  it to *goal-constructor*."
  [goal-constructor]
  (fn fresh-goal [{:keys [s-map next-id] :as state}]
    (let [goal (goal-constructor (lvar next-id))]
     (goal (with-next-id state (inc next-id))))))

(defn ldisj
  "Logical disjuction ('or'). Construct a new goal that succeeds
  whenever *goal-1* or *goal-2* succeed. `merge-streams` is used on each
  goal's output to ensure fair scheduling between the two."
  [goal-1 goal-2]
  (fn disj-goal [state]
    (merge-streams (goal-1 state) (goal-2 state))))

(defn lconj
  "Logical conjunction ('and'). Construct a new goal that succeeds
  when both *goal-1* and *goal-2* succeed."
  [goal-1 goal-2]
  (fn conj-goal [state]
    (mapcat-stream (goal-1 state) goal-2)))



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
  [goal]
  `(fn delayed-goal-outer [state#]
     (fn delayed-goal-inner [] (~goal state#))))

(defmacro ldisj+
  "Extended version of the `ldisj` function. This one handles multiple
  arguments, instead of just two. It also automatically wraps each goal
  with `delay-goal`, so you don't need to worry about adding them yourself.

  (This does have a performance cost, but speed is not the point of this port)"
  ([goal] `(delay-goal ~goal))
  ([goal & goals] `(ldisj (delay-goal ~goal) (ldisj+ ~@goals))))

(defmacro lconj+
  "Like `ldisj+`, but for `lconj`."
  ([goal] `(delay-goal ~goal))
  ([goal & goals] `(lconj (delay-goal ~goal) (lconj+ ~@goals))))



;; ## <a name="reify"></a>Reificiation

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


(defn reify-state-first-var [{:keys [s-map]}]
  (let [v (walk* (lvar 0) s-map)]
    (walk* v (reify-s v {}))))

(defn reify-state-lvar [{:keys [s-map]} lvar]
  (let [v (walk* lvar s-map)]
    (walk* v (reify-s v {}))))


;;; ## <a name="interface"></a>Programmer interface

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
  declare multiple logic variables at once, and it takes care of the
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

(defn call-empty-state [goal]
  (goal empty-state))

(defmacro run* [fresh-var-vec & goals]
  `(->> (fresh [~@fresh-var-vec] ~@goals)
     call-empty-state
     stream-to-seq
     (map reify-state-first-var)))

(defmacro run [n fresh-var-vec & goals]
  `(take ~n (run* ~fresh-var-vec ~@goals)))
