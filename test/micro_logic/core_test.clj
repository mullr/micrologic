(ns micro-logic.core-test
  (:require [clojure.test :refer :all]
            [micro-logic.protocols :refer :all]
            [micro-logic.core :refer :all]
            [micro-logic.sequence :refer :all]
            ))

(def a (lvar :a))
(def b (lvar :b))

(deftest micro-logic-tests
  (testing "walk"
    (are [u s, val] (= (walk u s) val)
         42 {}, 42
         a {a 42}, 42
         a {a b, b 42}, 42
         ))

  (testing "unify"
    (are [u v, s] (= (unify u v {}) s)
         1 1, {}
         1 2, nil
         a 42, {a 42}
         42 a, {a 42}

         [1 2 3]   [1 2 3]     {}
         [1 2 a]   [1 2 3]     {a 3}
         [1 dot a] [1 2 3]     {a [2 3]}
         [1 dot a] [1]         {a []}
         [1 2 3]   [1 dot a]   {a [2 3]}
         ))

  (testing "goals"
    (testing "basic"
      (are [g, s c] (= (stream-to-seq (g empty-state))
                       [(make-state s c)])
           (=== 1 1), {} 0
           (=== a 1), {a 1} 0
           (=== 1 a), {a 1} 0

           (call-fresh (fn [x] (=== x 1))), {(lvar 0) 1} 1
           ))

    (testing "composite"
      (are [g, states] (= (stream-to-seq (g empty-state))
                          states)
           (ldisj (=== a 1) (=== 2 2)), [(make-state {a 1} 0)
                                         (make-state {} 0)]

           (ldisj (=== a 1) (=== a 2)), [(make-state {a 1} 0)
                                         (make-state {a 2} 0)]

           (ldisj+ (=== a 1) (=== a 2)), [(make-state {a 1} 0)
                                          (make-state {a 2} 0)]


           (lconj (=== a 1) (=== b 2)), [(make-state {a 1, b 2} 0)]

           (lconj (=== a 1) (=== a 2)), []


           (delay-goal (=== a 1)), [(make-state {a 1} 0)]

           (conde [(=== a 1)] [(=== a 2)]), [(make-state {a 1} 0)
                                             (make-state {a 2} 0)]

           (fresh [x] (=== x 42)), [(make-state {(lvar 0) 42} 1)]

           (fresh [x y] (=== x 42) (=== y x)), [(make-state {(lvar 0) 42, (lvar 1) 42} 2)]
           )))

  (testing "scheduling"
    (letfn [(fives [x] (conde
                         [(=== x 5)]
                         [(fives x)]))

            (sixes [x] (conde
                         [(=== x 6)]
                         [(sixes x)]))

            (fives-and-sixes [x] (conde
                                   [(fives x)]
                                   [(sixes x)]))]

      (is (= [5 5 5 5 5]
             (run 5 [q] (fives q))))

      (is (= [6 6 6 6 6]
             (run 5 [q] (sixes q))))

      (is (= [5 6 5 6 5]
             (run 5 [q] (fives-and-sixes q))))
      ))

  (testing "deep-walk"
    (are [lvar s-map, value] (= value (deep-walk lvar s-map))

         a {},        a
         a {a 2},     2
         a {a b},     b
         a {a b, b 2} 2

         a {a [1 2 b], b 3} [1 2 3]
         a {a [1 2 b]}      [1 2 b]

         ))

  (testing "sequence goals"
    (are [goal, result] (= result (first (run 1 [q] goal)))

         (conso 1 [2 3] q)          [1 2 3]
         (conso q [2 3] [1 2 3])    1
         (conso 1 q     [1 2 3])    [2 3]

         (firsto q                  [1 2 3]) 1
         (firsto 1 q)               [1 dot '_.0]

         (resto q [1 2 3])          [2 3]
         (resto [2 3] q)            ['_.0 2 3]

         (fresh [x y z a b]
           (=== x 1)
           (=== y 2)
           (conso y '() a)
           (conso x a q))           [1 2]

         )
    )
  )
