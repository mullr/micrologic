(ns micro-logic.core
  (:require [micro-logic.protocols :refer :all]))

;;; Variable defs
;;; c: lvar id
;;; s: substitution map
;;; u, v: either literal values or logic variables.

(defrecord LVar [c])
(defn lvar [c] (LVar. c))
(defn lvar? [x] (= LVar (class x)))

(extend-protocol IWalk
  LVar
  (walk [u s] (if-let [val (get s u)]
                (walk val s)
                u))
  Object
  (walk [u s] u)

  nil
  (walk [u s] nil))

(defn unify [u v s]
  (let [u (walk u s),  v (walk v s)
        ulv (lvar? u), vlv (lvar? v)]
    (cond
      (and ulv vlv (= u v)) s
      ulv (assoc s u v)
      vlv (assoc s v u)
      (= u v) s
      :default (unify-terms u v s))))


(extend-protocol IUnifyTerms
  Object
  (unify-terms [u v s]
    (if (= u v) s)))



(declare lcons lcar lcdr lcons?)


(def mzero nil)
(defn unit [s] (lcons s nil))

(extend-protocol IScheduleSeq
  clojure.lang.IFn
  (mplus [$1 $2] #(mplus $2 ($1)))
  (bind  [$ g]   #(bind ($) g))

  nil
  (mplus [$1 $2] $2)
  (bind  [$ g] mzero))


;;; lcons


(defrecord LCons [car cdr]
  IUnifyTerms
  (unify-terms [u v s]
    (when (lcons? v)
      (->> s
        (unify (lcar u) (lcar v))
        (unify (lcdr u) (lcdr v)))))

  IScheduleSeq
  (mplus [$1 $2] (lcons (lcar $1)
                        (mplus (lcdr $1) $2)))
  (bind  [$ g]   (mplus (g (lcar $))
                        (bind (lcdr $) g))))

(defn lcons [a b] (LCons. a b))
(defn lcar [lc] (:car lc))
(defn lcdr [lc] (:cdr lc))
(defn lcons? [x] (= LCons (class x)))

(defmethod print-method LCons [lc ^java.io.Writer w]
  (.write w "(") (print-method (lcar lc) w) (.write w " . ") (print-method (lcdr lc) w) (.write w ")"))

(defn seq->lcons [s]
  (if (seq s)
    (lcons (first s) (seq->lcons (rest s)))
    nil))


;;; goal constructors

(defrecord State [s c])
(defn state [s c] (State. s c))
(def empty-state (state {} 0))

(defn === [u v]
  (fn [{:keys [s c]}]
    (if-let [s' (unify u v s)]
      (unit (state s' c))
      mzero)))

(defn call-fresh [f]
  (fn [{:keys [s c]}]
    ((f (lvar c)) (state s (inc c)))))

(defn ldisj [g1 g2]
  (fn [state]
    (mplus (g1 state) (g2 state))))

(defn lconj [g1 g2]
  (fn [state]
    (bind (g1 state) g2)))


;;; aux macros

(defmacro delay-goal [g]
  `(fn [state#]
     #(~g state#)))

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

;;; stream utils

(defn pull [$]
  (if (fn? $)
    (pull ($))
    $))

(defn stream-to-seq [$]
  (lazy-seq
   (let [$' (pull $)]
     (if (nil? $')
       '()
       (cons (lcar $') (stream-to-seq (lcdr $')))))))

;;; reification

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
