
;; COMMENT Header

(ns micro-logic.core
  (:require [micro-logic.protocols :refer :all]))

;; Logic Variables
;; The purpose of a logic program is to take an expression with some
;; unknowns in it and try to find values for those unknowns that make the
;; expression true. Here's an example logic program in English with an
;; unknown /x/:

;; #+begin_src
;;   Either x is the beginning of the list ["banana", "orange", "apple"],
;;   or x is the number 1.
;; #+end_src

;; (The two values of /x/ that make this expression true are ~1~ and ~banana~)

;; These unknowns are called /logic variables/, or /lvars/ for
;; short. Since we're going to write our logic programs in Clojure, we
;; need a way to represent them in that context.

(defrecord LVar [id])
(defn lvar [id] (LVar. id))
(defn lvar? [x] (instance? LVar x))

;; Adding entries
;; Although a substitution map is nothing but a regular clojure map, we
;; need some utility functions to deal with some subtleties of its behavior.
;; The first is for adding add new entries:

(defn add-substitution [s-map lvar value]
  (when s-map
    (assoc s-map lvar value)))

;; Looking up values
;; The other thing we do with a substitution map is to look up what value
;; is associated with an lvar. It's just a hash-map, so why don't we just
;; use the ~get~ function for this? Two reasons:

;; 1. If there is an lvar on the right-hand side, we need to look up that
;;    value, following such references until we get to a non-lvar.

;; 2. The operation we want is actually "give me the value of this
;;    object, given this substitution map". So if you call it with a
;;    value that's not an lvar, it should just give you that value back.

;; The function is called /walk/, since it follows lvar references on the
;; right-hand side.

(extend-protocol IWalk
  LVar
  (walk [u s-map] (if-let [val (get s-map u)]
                    (recur val s-map)
                    u))
  Object
  (walk [u s-map] u)

  nil
  (walk [u s-map] nil))

;; Here's the implementation of ~unify~:

(defn unify [u v s-map]
  (let [u (walk u s-map),    v (walk v s-map)
        u-is-lvar (lvar? u), v-is-lvar (lvar? v)]
    (cond
      ;; Terms that walk to equal values always unify, but add nothing
      ;; to the substitution map
      (= u v) s-map

      ;; Unifying an lvar term with some other value creates a new entry in
      ;; the substitution map
      u-is-lvar (add-substitution s-map u v)
      v-is-lvar (add-substitution s-map v u)

      ;; Unifying two terms that walk to non-lvar values is delegated
      ;; to the polymorphic unify-terms function, from IUnifyTerms.
      :default (unify-terms u v s-map))))

;; Here are the basic IUnifyTerms definitions for Object and nil.  If we
;; get dispatched to either of these definitions, we know that neither u
;; nor or v walks to an lvar, that the values aren't equal, and we aren't
;; doing some kind of extended unification that's defined
;; elsewhere. Thus, they must not unify.

(extend-protocol IUnifyTerms
  Object (unify-terms [u v s-map] nil)
  nil    (unify-terms [u v s-map] nil))

;; Empty stream

(def empty-stream
  (reify IStream
    (merge-streams [this other-stream] other-stream)
    (mapcat-stream [this g] this)
    (realize-stream-head [this] this)
    (stream-to-seq [this] '())))

;; Mature streams (StreamNode)
;; A mature streams is represented by an instance of StreamNode.  This is
;; kind of like a linked list: /head/ is the realized value that can be
;; taken from the stream, and /next/ is the stream which follows.  But
;; these streams are polymorphic; /next/ isn't necessarily a StreamNode,
;; just some other thing which extends the IStream protocol.

;; Note that if we have only StreamNodes (i.e. fully realized streams),
;; ~merge-streams~ is equivalent to ~concat~ and ~mapcat-stream~ to
;; ~mapcat~.

(deftype StreamNode [head next]
  IStream
  (merge-streams [this other-stream] (StreamNode. head
                                                  (merge-streams next other-stream)))
  (mapcat-stream [this g] (merge-streams (g head)
                                         (mapcat-stream next g)))
  (realize-stream-head [this] this)

  (stream-to-seq [this] (lazy-seq (cons head (stream-to-seq next)))))

(defn make-stream [s] (StreamNode. s empty-stream))

;; Definition
;; Here is the whole definition of IStream for functions:

(extend-protocol IStream
  clojure.lang.IFn
  (merge-streams [this other-stream]
    #(merge-streams other-stream (this)))

  (mapcat-stream [this g]
    #(mapcat-stream (this) g))

  (realize-stream-head [this]
    (trampoline this))

  (stream-to-seq [this]
    (stream-to-seq (realize-stream-head this))))

;; Interpreter state
;; A /state/ is a record containing a substitution map *s-map* and the id
;; of the next unused logic variable, /next-id/.

(defrecord State [s-map next-id])

(defn make-state [s-map next-id] (State. s-map next-id))
(def empty-state (make-state {} 0))
(defn with-s-map [state s-map] (assoc state :s-map s-map))
(defn with-next-id [state next-id] (assoc state :next-id next-id))

;; Basic goal constructors
;; Rather than dealing with goals directly, we usually use
;; /goal constructors/; given some parameter (usually a unification term or
;; another goal), they will return a goal function which closes over
;; it.

;; The most fundamental goal constructor is for unification.  Given two
;; terms /u/ and /v/, this creates a goal that will unify them. The goal
;; takes an existing state and returns (as a lazy stream) either a state
;; with bindings for the lvars in /u/ and /v/ (using ~unify~), or nothing
;; at all if /u/ and /v/ cannot be unified.

(defn === [u v]
  (fn unify-goal [{:keys [s-map] :as state}]
    (if-let [s-map' (unify u v s-map)]
      (make-stream (with-s-map state s-map'))
      empty-stream)))

;; /call-fresh/ is a higher-order goal constructor that encapsulates the
;; allocation of logic variables. You pass it your own
;; /goal-constructor/, which takes as its single parameter the lvar that
;; you want to use.  /call-fresh/ will make a new goal that allocates it
;; for you, passing it in to your code.  /goal-constructor/. For a more
;; convenient way to do this, see the /fresh/ macro below.

(defn call-fresh [goal-constructor]
  (fn fresh-goal [{:keys [s-map next-id] :as state}]
    (let [goal (goal-constructor (lvar next-id))]
     (goal (with-next-id state (inc next-id))))))

;; One way to combine smaller goals into a new one is with logical
;; disjunction, the 'or' operation. ~ldisj~ which constructs a new goal
;; that succeeds whenever /goal-1/ or /goal-2/ succeeds.  Another way to
;; look at this is that it interleaves the results of /goal-1/ and
;; /goal-2/, using ~merge-streams~.

(defn ldisj [goal-1 goal-2]
  (fn disj-goal [state]
    (merge-streams (goal-1 state) (goal-2 state))))

;; You can also combine goals with logical conjunction, the 'and'
;; operation. ~lconj~ constructs a new goal that succeeds when both
;; /goal-1/ and /goal-2/ succeed. It does this by running goal-2 on each
;; output of goal-1. You can think of this as being like function
;; composition for functions with multiple outputs.

(defn lconj [goal-1 goal-2]
  (fn conj-goal [state]
    (mapcat-stream (goal-1 state) goal-2)))

;; Auxiliary macros
;; /delay-goal/ will wrap the given goal in a new one which, when
;; executed, simply returns a thunk that wraps the goal. Recall that goal
;; functions return streams, and that a function is a valid kind of
;; stream (an immature stream). The goal will finally be executed when
;; the thunk is evaluated by realize-stream-head.

;; This is especially useful when defining recursive goals.

(defmacro delay-goal [goal]
  `(fn ~'delayed-goal-outer [state#]
     (fn ~'delayed-goal-inner [] (~goal state#))))

;; We also define extended versions of the ~ldisj~ and ~lconj~
;; functions. These handle multiple goal parameters, instead of just
;; two. They also automatically wraps each goal with ~delay-goal~, so you
;; don't need to worry about adding delays yourself.

;; (This does have a performance cost, but speed is not the point of this
;; implementation)

(defmacro ldisj+
  ([goal] `(delay-goal ~goal))
  ([goal & goals] `(ldisj (delay-goal ~goal) (ldisj+ ~@goals))))

(defmacro lconj+
  ([goal] `(delay-goal ~goal))
  ([goal & goals] `(lconj (delay-goal ~goal) (lconj+ ~@goals))))

;; Reificiation
;; In miniKanren, reification refers to extracting the desired values
;; from the stream of states you get as a result of executing a goal.

;; When there are logic variables in the output which were not assigned
;; a value, they are named ~_.0~, ~_.1~, and so on.

(defn reify-name [n]
  (symbol (str "_." n)))

;; /reify-s-map/ creates a substitution map with reified values in it. It
;; bases this on the supplied /s-map/ parameter, but adds entries for
;; each unknown that appears in the supplied term /v/, using values from
;; /reify-name/.

(defn reify-s [v s-map]
  (reify-s* (walk v s-map) s-map))

(extend-protocol IReifySubstitution
  LVar
  (reify-s* [v s-map] (let [n (reify-name (count s-map))]
                        (add-substitution s-map v n)))

  Object
  (reify-s* [v s-map] s-map)

  nil
  (reify-s* [v s-map] s-map))

;; /deep-walk/ is like walk, but instead of simply returning any
;; non-lvar value, it will attempt to assign values to any lvars
;; embedded in it.  For example, ~(deep-walk a {a (1 2 c), c 3)}~ will
;; give ~(1 2 3)~. (once we have the sequence extensions, which are
;; defined below)

(defn deep-walk [v s-map]
  (deep-walk* (walk v s-map) s-map))

(extend-protocol IDeepWalk
  LVar   (deep-walk* [v s-map] v)
  Object (deep-walk* [v s-map] v)
  nil    (deep-walk* [v s-map] v))

;; Finally, we can define the actual reifier. Given a state, this will
;; give you the reified value of the first lvar that was defined. If
;; you're using the /run/ macro defined below, this will be the first
;; query variable.

(defn reify-state-first-var [{:keys [s-map]}]
  (let [v (deep-walk (lvar 0) s-map)]
    (deep-walk v (reify-s v {}))))

;; will produce two results: ~{a 1, b 2}~ and ~{a 7, b 12}~. (If you've
;; never used miniKanren or core.logic before: 'e' means 'either'. Yes,
;; the naming is odd. But really, it's best to remember that it's an 'or
;; of ands' and to get used to the name)

(defmacro conde
  [& clauses]
  `(ldisj+ ~@(map (fn [clause]
                    `(lconj+ ~@clause))
                  clauses)))

;; The ~fresh~ macro allocates some new logic variables and makes them
;; available in its body. Really, it's a more convenient syntax for
;; ~call-fresh~. ~fresh~ lets you declare multiple logic variables at
;; once, and it takes care of the function declaration mechanics for you.

(defmacro fresh
  [var-vec & clauses]
  (if (empty? var-vec)
    `(lconj+ ~@clauses)
    `(call-fresh (fn [~(first var-vec)]
                   (fresh [~@(rest var-vec)]
                     ~@clauses)))))

;; Will give one result, ~{x 1, y 2}~.


;; We define a small utility to invoke a goal with an empty state, as you
;; might do when running a logic program from the top:

(defn call-empty-state [goal]
  (goal empty-state))

;; Finally, the run* macro gives us a lazy sequence of readable (reified) values.

(defmacro run* [fresh-var-vec & goals]
  `(->> (fresh [~@fresh-var-vec] ~@goals)
     call-empty-state
     stream-to-seq
     (map reify-state-first-var)))

;; If you only want a few values (for example, if you know there are an
;; infinite number of results), ~(run n [q] <<goals>>)~ can do that. It's
;; equivalent to running ~take~ on the output of run*.

(defmacro run [n fresh-var-vec & goals]
  `(take ~n (run* ~fresh-var-vec ~@goals)))
