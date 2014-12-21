(ns micro-logic.protocols)

(defprotocol IWalk
  (walk [u s]))

(defprotocol IScheduleSeq
  (mplus [$1 $2])
  (bind [$ g]))

(defprotocol IUnifyTerms
  (unify-terms [u v s]))
