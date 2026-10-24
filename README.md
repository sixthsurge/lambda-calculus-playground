experimenting with the lambda calculus for fun and learning :)

no LLMs were used for this project (for research or programming).

### usage

There are two modes: `untyped`, the untyped lambda calculus, and `stlc`, which is a simply typed 
lamda calculus extended with a fixed-point combinator. The default 
mode is `untyped`. Select the mode by passing `--mode=...`.

The `untyped` mode has one type, `Everything`, which is the type of everything, and no constants.

The `stlc` mode has the following types:
- `Int`
- `A -> B` where `A` and `B` are types
- `Fix` - the type of the fixed-point combinator (this models `forall a. (a -> a) -> a`).
...and the following constants:
- Numerals `0`, `1`, `2`, etc.
- Selection function `if`.
  - `if` follows the convention that zero is false.
- Built-in arithmetic functions
  - `add`
  - `sub`
  - `mul`
  - `div`
    - `div a 0` returns `0`.
- The fixed-point combinator `fix`.

Conventions:
- write lambda terms according to the following conventions:
  - `\` is used for lambda as it's easier to type
  - application binds closer than abstraction, so `\a.b c` is parsed as `\a.(b c)`, not `(\a.b) c`
  - application is left-associative - `a b c` is `(a b) c`
  - I allow the shorthand uncurried syntax for curried functions, like `\x y. x` instead of `\x. \y. x`
- you can add symbols to the dictionary by writing `name = definition` where the definition is a lambda
  term. before each term is reduced, all `(symbol_name, symbol_definition)` pairs in the dictionary are added to it by
  repeatedly surrounding the term in `(\symbol_name. term) symbol_definition`
- additionally I have a concept of "modifiers" which are written a bit like Rust macros (`name!(arg1, arg2 ...)`)
  - these are intended as helpers which transform the term as it is parsed
  - the most useful of these is cnum! which creates a Church numeral, for example `cnum!(4) => \f
    x. f (f (f (f x)))`
- additionally I have a concept of commands which are not part of the parse tree. Commands start
  with a `!`. The most useful one is `!load` which loads definitions from a file, for example 
  `!load examples/math.untyped`

### references
- https://en.wikipedia.org/wiki/Lambda_calculus
- http://pl.postech.ac.kr/~gla/pl2007/notes/deBruijn.pdf
- https://tromp.github.io/cl/diagrams.html
