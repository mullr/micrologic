# micro-logic

A literate Clojure implementation of microKanren. Read the annotated source
at http://mullr.github.io/micrologic/literate.html.

This is largely based on microKanren, an even more minimalistic version of miniKanren.
- http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf



microLogic can be thought of as the core.logic parallel of
microKanren. It has simplified verisons of some of the same concepts,
namely the extensible unifier. By reading the code and documentation,
you can understand more about how core.logic works.

It may also be a suitable base for experimenting with new logic
programming ideas, because of its simplicity.

## Usage

```clojure
(ns my.ns
  [micro-logic.protocols :refer :all]
  [micro-logic.core :refer :all])

(run 1 [q]
  (conde
    [(=== q 1)]
    [(=== q 2)]))

 => (1 2)
 ```



## Differences from microKanren

Polymorphic dispatch via protocols is used in place of `(cond)` with
type checks, where possible.

Clojure-native datatypes are used where appropriate
- The substitution map is a clojure map instead of an alist
- There is an LVar defrecrord, instead of using a vector of c
- We have an explicit StreamNode data type, rather building on the
  built-in list type
- Clojure doesn't allow improper lists; LListCell is a linked list
  which does.

Many names have changed to be more clojure-like:

|uKanren | microLogic          |
|--------|---------------------|
|mplus   | merge-streams       |
|bind    | mapcat-stream       |
|pull    | realize-stream-head |
|mzero   | empty-stream        |
|unit    | stream              |
|Zzz     | delay-goal          |
|conj    | lconj               |
|disj    | ldisj               |
|==      | ===                 |


## Differences from core.logic

|core.logic | microLogic           |
|-----------|----------------------|
|mplus      | merge-streams        |
|bind       | mapcat-stream        |
|pull       | realize-stream-head  |
|mzero      | empty-stream         |
|unit       | stream               |
|==         | ===                  |
|LCons      | LListCell            |



## References

- The microKanren paoper:http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf
- The microKanren scheme implementation: https://github.com/jasonhemann/microKanren
- core.logic, Clojure's real miniKanren implementation: https://github.com/clojure/core.logic
- The Will Byrd's dissertation on miniKanren: https://github.com/webyrd/dissertation-single-spaced/raw/master/thesis.pdf

## License

Copyright © 2014 Russell Mull

Distributed under the Eclipse Public License either version 1.0 or (at
your option) any later version.