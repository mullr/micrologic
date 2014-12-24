
;; COMMENT Header

(ns micro-logic.core
  (:require [micro-logic.protocols :refer :all]))

;; Logic Variables
;; Logic variables (lvars for short) are the unknown items that will be
;; given a value by the unifier. Each of them has an id; this is a number
;; which is assigned when a new variable is allocated.

(defrecord LVar [id])
(defn lvar [id] (LVar. id))
(defn lvar? [x] (instance? LVar x))

;; Substitutions and Walking
;; A substitution map (/s-map/) is a hash-map that gives
;; mappings from logic variables to their values.

;; To see what value an lvar is bound to in a given substitution map,
;; use ~(walk u s)~. (/u/ is an lvar or a value) Supposing /a/ and /b/
;; are lvars; in this simple case, ~(walk a {a 1})~ returns ~1~.

;; Minikanren derivatives (including this one) use /triangular/
;; substitutions, which means that an lvar may map to another lvar.
;; Walk will follow these variable references until a value is
;; reached. For example, ~(walk a {a b, b 2})~ returns ~2~.

;; The observant reader may note that it is easy to construct a
;; substitution map with a loop in it: ~(walk a {a b, b a})~ will not
;; terminate. This case may be handled (but is not, in this
;; implementation) with an ~occurs-check~ function call when adding
;; new substitutions.

;; We implement this in Clojure with the IWalk protocol, since it is
;; polymorphic on the type of /u/.

;; Note: when walking for an lvar, it may not be present in the
;; substitution map.  In this case, the lvar itself is returned,
;; indicating that the lvar is currently unbound.

(extend-protocol IWalk
  LVar
  (walk [u s-map] (if-let [val (get s-map u)]
                    (recur val s-map)
                    u))
  Object
  (walk [u s-map] u)

  nil
  (walk [u s-map] nil))

(defn add-substitution [s-map lvar value]
  (when s-map
    (assoc s-map lvar value)))

;; Unification
;; Given two terms /u/ and /v/, and an existing substitution map /s/,
;; unify produces a new substitution map with mappings that will make u
;; and v equal.

;; This unifier is extensible, in the spirit of core.logic. Only
;; unification on basic types is directly implemented here. By extending
;; the IUnifyTerms protocol, special unification logic may be supplied
;; for any data type.

;; A /term/ is, somewhat circularly, something you can pass to the
;; unifier.  this includes lvars, regular values, and values of any type
;; to which you have extended IUnifyTerms.

(defn unify [u v s-map]
  (let [u (walk u s-map),    v (walk v s-map)
        u-is-lvar (lvar? u), v-is-lvar (lvar? v)]
    (cond
      ;; Unifying two lvars adds no information to the substitution map
      (and u-is-lvar v-is-lvar (= u v)) s-map

      ;; Unifying an lvar with some other value creates a new entry in
      ;; the substitution map
      u-is-lvar (add-substitution s-map u v)
      v-is-lvar (add-substitution s-map v u)

      ;; two not-lvar but equal structures unify
      (= u v) s-map

      ;; Unifying two non-lvars is delegated to the polymorphic
      ;; unify-terms function, from IUnifyTerms.
      :default (unify-terms u v s-map))))

;; If we get dispatched to either of these definitions, we know that neither
;; u or v is an lvar, that they aren't equal, and we aren't doing some kind
;; of structural comparison defined elsewhere. They must not unify.

(extend-protocol IUnifyTerms
  Object (unify-terms [u v s-map] nil)
  nil    (unify-terms [u v s-map] nil))

;; Empty stream

(def empty-stream
  (reify IStream
    (merge-streams [stream-1 stream-2] stream-2)
    (mapcat-stream [stream g] stream)
    (realize-stream-head [stream] stream)
    (stream-to-seq [stream] '())))

;; Mature streams (StreamNode)

;; A head-realized streams is represented by an instance of StreamNode.
;; This is kind of like a linked list: /head/ is the realized value that
;; can be taken from the stream, and /next/ is the stream which follows.
;; But these streams are polymorphic; /next/ isn't necessarily a
;; StreamNode, just some other thing which extends the IStream protocol.

;; Note that, if we have only StreamNodes (i.e. fully realized streams),
;; ~merge-streams~ is equivalent to ~concat~ and ~mapcat-stream~ to
;; ~mapcat~.

(deftype StreamNode [head next]
    IStream
    (merge-streams [stream-1 stream-2] (StreamNode. head
                                        (merge-streams next stream-2)))
    (mapcat-stream [stream g] (merge-streams (g head)
                                        (mapcat-stream next g)))
    (realize-stream-head [stream] stream)

    (stream-to-seq [stream] (lazy-seq (cons head (stream-to-seq next)))))

(defn make-stream [s] (StreamNode. s empty-stream))

;; Definition
;; Here is the whole definition of IStream for functions:

(extend-protocol IStream
  clojure.lang.IFn
  (merge-streams [stream-1 stream-2]
    #(merge-streams stream-2 (stream-1)))

  (mapcat-stream [stream g]
    #(mapcat-stream (stream) g))

  (realize-stream-head [stream]
    (trampoline stream))

  (stream-to-seq [stream]
    (stream-to-seq (realize-stream-head stream))))

;; Goals
;; A /state/ is a record containing a substitution map *s* and the id
;; of the next unbound /next-id/.

(defrecord State [s-map next-id])

(defn make-state [s-map next-id] (State. s-map next-id))
(def empty-state (make-state {} 0))
(defn with-s-map [state s-map] (assoc state :s-map s-map))
(defn with-next-id [state next-id] (assoc state :next-id next-id))

;; Basic goal constructors

;; Given two terms u and v, create a goal that will unify them. The
;; goal takes an existing state and returns either a state with
;; bindings for the lvars in u and v (using ~unify~), or returns the empty
;; stream if no such state exists.

(defn === [u v]
  (fn unify-goal [{:keys [s-map] :as state}]
    (if-let [s-map' (unify u v s-map)]
      (make-stream (with-s-map state s-map'))
      empty-stream)))

;; Wrap /goal-constructor/, a function of a single lvar, in a
;; goal that allocates a new lvar from its state parameter and passes
;; it to /goal-constructor/.

(defn call-fresh [goal-constructor]
  (fn fresh-goal [{:keys [s-map next-id] :as state}]
    (let [goal (goal-constructor (lvar next-id))]
     (goal (with-next-id state (inc next-id))))))

;; Logical disjuction ('or'). Construct a new goal that succeeds
;; whenever /goal-1/ or /goal-2/ succeed. ~merge-streams~ is used on each
;; goal's output to ensure fair scheduling between the two.

(defn ldisj [goal-1 goal-2]
  (fn disj-goal [state]
    (merge-streams (goal-1 state) (goal-2 state))))

;; Logical conjunction ('and'). Construct a new goal that succeeds when
;; both /goal-1/ and /goal-2/ succeed.

(defn lconj [goal-1 goal-2]
  (fn conj-goal [state]
    (mapcat-stream (goal-1 state) goal-2)))

;; Auxilliary macros
;; At this point, we have defined everything we need to do logic
;; programming.  But it's very inconvenient; some utility macros make the
;; task more bearable.

;; Wrap the given goal in a new one which, when executed, simply
;; returns a thunk. Recall that goal functions return streams, and that
;; a function is a valid kind of stream (an immature stream). The goal
;; will finally be executed when the thunk is evaluated by
;; realize-stream-head.

;; This is useful for defining recursive goals.

(defmacro delay-goal [goal]
  `(fn delayed-goal-outer [state#]
     (fn delayed-goal-inner [] (~goal state#))))

;; Extended version of the ~ldisj~ function. This one handles multiple
;; arguments, instead of just two. It also automatically wraps each goal
;; with ~delay-goal~, so you don't need to worry about adding them yourself.

;; (This does have a performance cost, but speed is not the point of this port)

(defmacro ldisj+
  ([goal] `(delay-goal ~goal))
  ([goal & goals] `(ldisj (delay-goal ~goal) (ldisj+ ~@goals))))

;; Like ~ldisj+~, but for ~lconj~.

(defmacro lconj+
  ([goal] `(delay-goal ~goal))
  ([goal & goals] `(lconj (delay-goal ~goal) (lconj+ ~@goals))))

;; Reificiation

;; In miniKanren, reification refers to extracting the desired values
;; from the stream of states you get as a result of executing a goal.

(defn reify-name [n]
  (symbol (str "_." n)))

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

;; Like walk. But instead of simply returning any non-lvar value, will
;; attempt to assign values to any lvars embedded in the value.  For
;; example, ~(walk* a {a (1 2 c), c 3)}~ will give ~(1 2 3)~.  (once we
;; have the sequence extensions from sequence.clj)

(defn walk* [v s-map]
  (deep-walk (walk v s-map) s-map))

(extend-protocol IDeepWalk
  LVar   (deep-walk [v s-map] v)
  Object (deep-walk [v s-map] v)
  nil    (deep-walk [v s-map] v))

(defn reify-state-first-var [{:keys [s-map]}]
  (let [v (walk* (lvar 0) s-map)]
    (walk* v (reify-s v {}))))

;; will produce two results: ~{a 1, b 2}~ and ~{a 7, b 12}~.

(defmacro conde
  [& clauses]
  `(ldisj+ ~@(map (fn [clause]
                    `(lconj+ ~@clause))
                  clauses)))

;; Will give one result, ~{x 1, y 2}~.

(defmacro fresh
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
