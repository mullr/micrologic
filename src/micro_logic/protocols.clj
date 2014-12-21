(ns micro-logic.protocols)

(defprotocol IWalk
  (walk [u s]))

(defprotocol IDeepWalk
  (deep-walk [v s]))

(defprotocol IUnifyTerms
  (unify-terms [u v s]))

(defprotocol IStream
  (mplus [$1 $2])
  (bind [$ g])
  (pull [$]))
