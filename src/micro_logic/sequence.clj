
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

;; Whenever you want an improper list in the context of a logic program,
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

;; The first extension point is the unifier; we need to define what it means
;; to unify a sequence with something else.

;; The basic case is simple: if unifying a sequence with another sequence,
;; then we should unify each element together. Recursively, this means unifying
;; their first elements and then the rest of the sequence.

;; The unifier also needs to be aware of the dot-notation described
;; above. If either /u/ or /v/ is a sequence beginning with a dot, the
;; its second item must be an lvar which should be unified with the other
;; variable. For example, if we start with ~(=== [1 2 3] [1 . a])~, it
;; will recurse down to ~(=== [2 3] [. a])~. Detecting that, we can call
;; ~(=== [2 3] a)~, which gives the desired result.

(extend-protocol IUnifyTerms
  clojure.lang.Sequential
  (unify-terms [u v s]
    (cond
      (= dot (first u)) (unify (second u) v s)
      (= dot (first v)) (unify u (second v) s)
      (seq v) (->> s
                (unify (first u) (first v))
                (unify (rest u) (rest v))))))

;; Next, we need to extend the reifier. When calling reify-s, we need to
;; look for occurrences of logic variables inside of given parameter. This
;; extends reify-s to make a recursive call on the first element of the
;; sequence, then on the remaining elements.

(extend-protocol IReifySubstitution
  clojure.lang.Sequential
  (reify-s* [v s-map]
    (if (seq v)
      (reify-s (rest v) (reify-s (first v) s-map))
      s-map)))

;; Deep-walk needs to be extended as well. As above, we we handle
;; sequences beginning with 'dot' as a special case, go recursing back
;; with the second item of the sequence.  For any other sequences, we
;; effectively map the deep-walk function over the sequence.

(extend-protocol IDeepWalk
  clojure.lang.Sequential
  (deep-walk* [v s-map]
    (cond
      (and (= dot (first v))
           (sequential? (second v)))
      (deep-walk (second v) s-map)

      (seq v)
      (cons (deep-walk (first v) s-map)
            (deep-walk (rest v)  s-map))

      :default v)))

;; Sequence goals
;; Now we can define some user-level goals for sequences. First,
;; conso says that /out/ is the sequence with the head /first/ and the
;; tail /rest/.

(defn conso [first rest out]
  (if (lvar? rest)
    (=== [first dot rest] out)
    (=== (cons first rest) out)))

;; /firsto/ simply says that /first/ is the head of /out/.

(defn firsto [first out]
  (fresh [rest]
    (conso first rest out)))

;; And /resto/, likewise, says that /rest/ is the tail of /out/.

(defn resto [rest out]
  (fresh [first]
    (conso first rest out)))

;; /emptyo/ is a way to say that /s/ must be an empty sequence.

(defn emptyo [s]
  (=== '() s))

;; /appendo/ says that /out/ is the result of appending the sequence parameters
;; /seq1/ and /seq1/.

(defn appendo [seq1 seq2 out]
  (conde
    [(emptyo seq1) (=== seq2 out)]
    [(fresh [first rest rec]
       (conso first rest seq1)
       (conso first rec out)
       (appendo rest seq2 rec))]))
