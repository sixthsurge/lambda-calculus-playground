experimenting with the lambda calculus for fun and learning :)

no LLMs were used for this project (for research or programming).

### usage

There are two modes: `untyped` and `stlc` (simply typed lamda calculus). The default
mode is `untyped`. Select the mode by passing `--mode=...`.

The `untyped` mode has one type, `Everything`, which is the type of everything.
The types in the `stlc` mode are `Int` and `(A -> B)` where `A` and `B` are types.
Additionally the stlc mode has the following constants:
- Any positive integer or 0
- The built-in functions add, sub, mul and div
  - div a 0 returns 0

Conventions:
- write lambda terms according to the following conventions:
  - `\` is used for lambda as it's easier to type
  - application binds closer than abstraction, so `\a.b c` is parsed as `\a.(b c)`, not `(\a.b) c`
  - application is left-associative - `a b c` is `(a b) c`
  - I allow the shorthand uncurried syntax for curried functions, like `\x y. x` instead of `\x. \y. x`
- you can add symbols to the dictionary by writing `name := definition` where the definition is a lambda
  term. before each term is reduced, all `(symbol_name, symbol_definition)` pairs in the dictionary are added to it by
  repeatedly surrounding the term in `(\symbol_name. term) symbol_definition`
- additionally I have a concept of "modifiers" which are written a bit like Rust macros (`name!(arg1, arg2 ...)`)
  - these are intended as helpers which transform the term as it is parsed
  - the most useful of these is cnum! which creates a Church numeral, for example `cnum!(4) => \f
    x. f (f (f (f x)))`
- additionally I have a concept of commands which are not part of the parse tree. Commands start
  with a `!`. The most useful one is `!load` which loads definitions from a file, for example 
  `!load input/math`

### references
- https://en.wikipedia.org/wiki/Lambda_calculus
- http://pl.postech.ac.kr/~gla/pl2007/notes/deBruijn.pdf
- https://tromp.github.io/cl/diagrams.html
