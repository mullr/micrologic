(ns micro-logic.sequence
  (:require [micro-logic.core :refer :all]
            [micro-logic.protocols :refer :all]))

;; ## Sequence support
;;
;; The base logic programming system has unification and reification
;; support for only lvars and basic values. But it's done in an
;; extensible way. We'll now proceed to add sequence support to the
;; base language.

;; Unfortunately, the regular clojure list type isn't sufficient for
;; our purposes. There are many cases where we want to unify against
;; the tail of a sequence, which means putting an lvar in the tail
;; position.  Standard minikanren uses imporoper lists for this. For
;; example, `(1 . a)` may be unified against a with another list to
;; match all lists beginning with 1, assigning the suffix to the lvar
;; *a*.
;;
;; We define here the LList (Logic List) type, which is a simple
;; linked list without that restriction. It extends
;; IPersistentCollection, Sequential, and ISeq so it can interoperate
;; with the clojure standard library


(declare lcons)

;; The singleton empty list is an instance of LListCell, to allow it to be dispatched
;; with the protocol system.
(def empty-llist
  (reify
    ILList
    (lfirst [_] nil)
    (lrest [self] self)

    clojure.lang.IPersistentCollection
    (seq [_] nil)
    (cons [self o] (lcons o self))
    (empty [self] self)
    (equiv [self o] (= (seq self) (seq o)))

    clojure.lang.Sequential
    clojure.lang.ISeq
    (first [_] nil)
    (next [_] nil)
    (more [_] nil)
    ))

(defn lempty? [x] (= empty-llist x))

(deftype LListCell [item next-cell]
  ILList
  (lfirst [lc] item)
  (lrest [lc] next-cell)

  clojure.lang.IPersistentCollection
  (seq [self] self)
  (cons [self o] (LListCell. o self))
  (empty [self] empty-llist)
  (equiv [self o] (if (instance? LListCell o)
                    (and (= item
                            (lfirst o))
                         (= next-cell (lrest o)))
                    false))

  clojure.lang.Sequential
  clojure.lang.ISeq
  (first [self] item)
  (next [self] (cond
                 (lempty? next-cell) nil
                 (instance? LListCell next-cell) next-cell
                 :default (list next-cell)))
  (more [self] (if (lempty? next-cell)
                 nil
                 (next self))))

;; Define a constructor and a type-test, which are useful shortcuts
;; below.
(defn lcons [a b] (LListCell. a b))
(defn llist? [x] (instance? LListCell x))

;; By extending IUnifyTerms, LList is able to participate in
;; unification. We use a simple recursive definition to say the
;; unifying two sequences means that we unify their elements.
(extend-protocol IUnifyTerms
  LListCell
  (unify-terms [u v s]
    (when (llist? v)
      (->> s
        (unify (lfirst u) (lfirst v))
        (unify (lrest u) (lrest v))))))

;; Extending IReifySubstitution and
(extend-protocol IReifySubstitution
  LListCell
  (reify-s* [v s] (reify-s (lrest v) (reify-s (lfirst v) s))))

;; Extending IDeepWalk allows
(extend-protocol IDeepWalk
  LListCell
  (deep-walk [v s] (lcons (walk* (lfirst v) s)
                          (if (lempty? (lrest v))
                            empty-llist
                            (walk* (lrest v) s)))))

;; Add support to the printer for our LList data type.  Print it like
;; a normal list unless it's an improper list; in that case, use '.'
;; notation. For example, `(lcons 1 (lcons 2 3))` will print as
;; `(1 2 . 3)`.
(defn print-llist [l ^java.io.Writer w]
  (cond
    (lempty? l) (do)
    (lempty? (lrest l)) (print-method (lfirst l) w)
    (llist? (lrest l)) (do
                         (print-method (lfirst l) w)
                         (.write w " ")
                         (recur (lrest l) w))
    :default (do (print-method (lfirst l) w)
                 (.write w " . ")
                 (print-method (lrest l) w))))

(defmethod print-method LListCell [l ^java.io.Writer w]
  (.write w "(") (print-llist l w) (.write w ")"))

(defn seq->llist
  "A utility function to construct llist a clojure seq."
  [s]
  (if (seq s)
    (lcons (first s) (seq->llist (rest s)))
    empty-llist))


;;; ## Sequence relations

(defn conso
  "Relation: *out* is an LList built out of *first* and *rest*"
  [first rest out]
  (=== (lcons first rest) out))

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
  (=== empty-llist x))

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
