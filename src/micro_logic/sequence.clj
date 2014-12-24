
;; COMMENT Header

(ns micro-logic.sequence
  (:require [micro-logic.core :refer :all]
            [micro-logic.protocols :refer :all]))

;; Extending the core
;; When we unify sequences, we'd like to be able to indicate that an lvar
;; should be associated with the tail of a sequence. In the scheme
;; implementation, this is easy: by placing an lvar in the tail position
;; of a linked list node (the cdr position of a cons node), the
;; unification happens naturally when walking down the list.

;; Since Clojure disallows putting non-list items in linked-list cells
;; (so-called 'improper lists'), we have to find another way to do
;; it. core.logic solves this problem by defining its own LCons data type
;; which does allow improper lists. We take a different approach here.

;; Whenver you want an improper list in the context of a logic program,
;; you can signify it with the 'dot' sigil. For example: ~[1 2 dot a]~.
;; This is meant to evoke the Scheme and Common LISP notation for
;; improper lists: ~(1 2 . 3)~. This will typically be transparent to the
;; user on the programming side, since such lists will be automatically
;; constructed by the 'conso' goal below.

(deftype Dot [])
(def dot (Dot.))

;; There are times when the user may see an improper list as the result
;; of a query. In this case, print the sigil as "."

(defmethod print-method Dot [l ^java.io.Writer w]
  (.write w "."))

(extend-protocol IUnifyTerms
  clojure.lang.Sequential
  (unify-terms [u v s]
    (cond
      (= dot (first u)) (unify (second u) v s)
      (= dot (first v)) (unify u (second v) s)
      (seq v) (->> s
                (unify (first u) (first v))
                (unify (rest u) (rest v))))))

;; Extending IReifySubstitution and
(extend-protocol IReifySubstitution
  clojure.lang.Sequential
  (reify-s* [v s-map]
    (if (seq v)
      (reify-s (rest v) (reify-s (first v) s-map))
      s-map)))


;; Extending IDeepWalk allows
(extend-protocol IDeepWalk
  clojure.lang.Sequential
  (deep-walk [v s-map]
    (cond
      (and (= dot (first v))
           (sequential? (second v)))
      (walk* (second v) s-map)

      (seq v)
      (cons (walk* (first v) s-map)
            (walk* (rest v)  s-map))

      :default v)))

;; Sequence relations

(defn conso
  "Relation: *out* is an LList built out of *first* and *rest*"
  [first rest out]
  (if (lvar? rest)
    (=== [first dot rest] out)
    (=== (cons first rest) out)))

(defn firsto
  "Relation: *out* is an LList whose first element is *first*"
  [first out]
  (fresh [rest]
    (conso first rest out)))

(defn resto
  "Relation: *out* is an LList whose cdr is *rest*"
  [rest out]
  (fresh [first]
    (conso first rest out)))

(defn emptyo
  "Relation: *x* is the empty LList"
  [x]
  (=== '() x))

(defn repeato [n out]
  (conde
    [(emptyo out)]
    [(fresh [rest]
       (conso n rest out)
       (repeato n rest))]))

(defn iterateo [gc x]
  (conde
    [(emptyo x)]
    [(fresh [val rest]
       (gc val)
       (conso val rest x)
       (iterateo gc rest))]))
