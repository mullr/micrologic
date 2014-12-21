(ns micro-logic.core
  (:require [micro-logic.protocols :refer :all]))

;; ## Common variables
;; - *c* The id of an lvar
;; - *s* A substitution map. Keys are lvars, values are either lvars or values.
;; - *u, v* Either an lvar or a literal value. Unification terms, more precisely.
;; - *g* A goal function. Given a substition map, produce a stream of substitution maps.
;; - *gc* Goal constructor function.
;; - *$* A stream: either a function, an lcons, or nil.


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
(extend-protocol IWalk
  LVar
  ;; When walking for a variable, it may not be present in the
  ;; substitution map.  In this case, the variable itself is returned,
  ;; indicating that the variable is currently unbound.
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

(def mzero
  (reify IStream
    (mplus [$1 $2] $2)
    (bind [$ g] $)
    (pull [$] $)))

(deftype StreamNode [current next]
  IStream
  (mplus [$1 $2] (StreamNode. current
                              (mplus next $2)))
  (bind [$ g] (mplus (g current)
                     (bind next g)))
  (pull [$] $))


(extend-protocol IStream
  clojure.lang.IFn
  (mplus [$1 $2] (fn mplus-fn [] (mplus $2 ($1))))
  (bind [$ g] (fn bind-fn  [] (bind ($) g)))
  (pull [$] (trampoline $)))

(defn unit [s] (StreamNode. s mzero))

(defn stream-to-seq [$]
  (lazy-seq
   (let [$' (pull $)]
     (if (= mzero $')
       '()
       (cons (.current $') (stream-to-seq (.next $')))))))

;;; goal constructors

(defrecord State [s c])
(defn state [s c] (State. s c))
(def empty-state (state {} 0))

(defn === [u v]
  (fn unify-goal [{:keys [s c]}]
    (if-let [s' (unify u v s)]
      (unit (state s' c))
      mzero)))

(defn call-fresh [f]
  (fn fresh-goal [{:keys [s c]}]
    ((f (lvar c)) (state s (inc c)))))

(defn ldisj [g1 g2]
  (fn disj-goal [state]
    (mplus (g1 state) (g2 state))))

(defn lconj [g1 g2]
  (fn conj-goal [state]
    (bind (g1 state) g2)))


;;; aux macros

(defmacro delay-goal [g]
  `(fn delayed-goal-outer [state#]
     (fn delayed-goal-inner [] (~g state#))))

(defmacro lconj+
  ([g] `(delay-goal ~g))
  ([g & gs] `(lconj (delay-goal ~g) (lconj+ ~@gs))))

(defmacro ldisj+
  ([g] `(delay-goal ~g))
  ([g & gs] `(ldisj (delay-goal ~g) (ldisj+ ~@gs))))

(defmacro conde [& clauses]
  `(ldisj+ ~@(map (fn [clause]
                    `(lconj+ ~@clause))
                  clauses)))

(defmacro fresh [var-vec & clauses]
  (if (empty? var-vec)
    `(lconj+ ~@clauses)
    `(call-fresh (fn [~(first var-vec)]
                   (fresh [~@(rest var-vec)]
                     ~@clauses)))))


;;; reification

(declare lcons lcar lcdr lcons?)


(defn reify-name [n]
  (symbol (str "_." n)))

(defn reify-s [v s]
  (let [v' (walk v s)]
    (cond
      (lvar? v') (let [n (reify-name (count s))]
                   (assoc s v' n))
      (lcons? v') (reify-s (lcdr v')
                           (reify-s (lcar v') s))
      :default s)))

(defn walk* [v s]
  (let [v' (walk v s)]
    (cond
      (lvar? v') v'
      (lcons? v') (lcons (walk* (lcar v') s)
                         (walk* (lcdr v') s))
      :default v')))

(defn reify-state-first-var [{:keys [s c]}]
  (let [v (walk* (lvar 0) s)]
    (walk* v (reify-s v {}))
    ))

(defn mk-reify [state-seq]
  (map reify-state-first-var state-seq))


;;; run interface

(defn call-empty-state [g]
  (g empty-state))

(defmacro run* [query-var-vec & gs]
  `(mk-reify
    (stream-to-seq
     (call-empty-state
      (fresh [~@query-var-vec]
        ~@gs)))))

(defmacro run [n query-var-vec & gs]
  `(take ~n (run* ~query-var-vec ~@gs)))


;;; lcons

(declare empty-lcons)
(deftype LCons [car cdr]
  clojure.lang.IPersistentCollection
  (seq [self] self)
  (cons [self o] (lcons o self))
  (empty [self] empty-lcons)
  (equiv [self o] (if (instance? LCons o)
                    (and (= car (.car o))
                         (= cdr (.cdr o)))
                    false))

  clojure.lang.Sequential
  clojure.lang.ISeq
  (first [self] car)
  (next [self] (cond
                 (instance? LCons cdr) cdr
                 :default (list cdr)))
  (more [self] (next self))

  IUnifyTerms
  (unify-terms [u v s]
    (when (lcons? v)
      (->> s
        (unify (lcar u) (lcar v))
        (unify (lcdr u) (lcdr v)))))

  IDeepWalk
  (deep-walk [v s] (LCons. (walk* car s)
                           (walk* cdr s))))


(defn lcons [a b] (LCons. a b))
(defn lcar [lc] (.car lc))
(defn lcdr [lc] (.cdr lc))
(defn lcons? [x] (instance? LCons x))

(def empty-lcons (lcons (Object.) (Object.)))
(defn lempty? [x] (= empty-lcons x))

(defn print-lcons [lc ^java.io.Writer w]
  (cond
    (lempty? lc) (do)
    (lempty? (lcdr lc)) (print-method (lcar lc) w)
    (instance? LCons (lcdr lc)) (do
                                  (print-method (lcar lc) w)
                                  (.write w " ")
                                  (recur (lcdr lc) w))
    :default (do (print-method (lcar lc) w)
                 (.write w " . ")
                 (print-method (lcdr lc) w))))

(defmethod print-method LCons [lc ^java.io.Writer w]
  (.write w "(") (print-lcons lc w) (.write w ")"))

(defn seq->lcons [s]
  (if (seq s)
    (lcons (first s) (seq->lcons (rest s)))
    empty-lcons))
