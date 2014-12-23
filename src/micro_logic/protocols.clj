(ns micro-logic.protocols)

(defprotocol IWalk
  (walk [u s]))

(defprotocol IDeepWalk
  (deep-walk [v s]))

(defprotocol IUnifyTerms
  (unify-terms [u v s]))

(defprotocol IStream
  (merge-streams [$1 $2])
  (mapcat-stream [$ g])
  (realize-stream-head [$])
  (stream-to-seq [$]))

(defprotocol IReifySubstitution
  (reify-s* [v s]))

(defprotocol ILList
  (lfirst [l])
  (lrest [l]))
