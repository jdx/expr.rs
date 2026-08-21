# Changelog


### Features

- Make the dependency tree optional ([#110](https://github.com/jdx/expr.rs/pull/110))


## [2.0.0] - 2026-08-19

### Bug Fixes

- *(deps)* Update rust crate strum to 0.28 ([#34](https://github.com/jdx/expr.rs/pull/34))
- *(lib)* Align go compatibility edge cases ([#91](https://github.com/jdx/expr.rs/pull/91))
- *(deps)* Update rust crate base64 to 0.23 ([#93](https://github.com/jdx/expr.rs/pull/93))
- *(lib)* Return errors for malformed built-in calls ([#100](https://github.com/jdx/expr.rs/pull/100))
- *(lib)* Align arithmetic edge cases ([#101](https://github.com/jdx/expr.rs/pull/101))
- *(parse)* Support dynamic ranges and slices ([#104](https://github.com/jdx/expr.rs/pull/104))
- *(lib)* Align unicode and collection edge cases ([#105](https://github.com/jdx/expr.rs/pull/105))
- *(lib)* Align arbitrary map key semantics ([#106](https://github.com/jdx/expr.rs/pull/106))
- *(lib)* Preserve temporal timezone semantics ([#109](https://github.com/jdx/expr.rs/pull/109))

### Documentation

- Document v2 status and migration ([#80](https://github.com/jdx/expr.rs/pull/80))

### Features

- Add expr conversion built-ins ([#71](https://github.com/jdx/expr.rs/pull/71))
- *(lib)* Align operators and add bitwise built-ins ([#73](https://github.com/jdx/expr.rs/pull/73))
- *(lib)* Add borrowed and serializable contexts ([#79](https://github.com/jdx/expr.rs/pull/79))
- *(parse)* Add go-compatible literal syntax ([#86](https://github.com/jdx/expr.rs/pull/86))
- *(lib)* Add numeric and utility built-ins ([#87](https://github.com/jdx/expr.rs/pull/87))
- *(lib)* Add collection utility built-ins ([#88](https://github.com/jdx/expr.rs/pull/88))
- *(lib)* Add aggregate predicate built-ins ([#89](https://github.com/jdx/expr.rs/pull/89))
- *(lib)* Add predicate indices and scientific literals ([#94](https://github.com/jdx/expr.rs/pull/94))
- *(lib)* Add byte values and literals ([#95](https://github.com/jdx/expr.rs/pull/95))
- *(parse)* Add multiline conditional expressions ([#97](https://github.com/jdx/expr.rs/pull/97))
- *(lib)* Add temporal values and functions ([#98](https://github.com/jdx/expr.rs/pull/98))
- *(lib)* Add non-string map keys ([#99](https://github.com/jdx/expr.rs/pull/99))
- *(lib)* Complete temporal compatibility ([#107](https://github.com/jdx/expr.rs/pull/107))

### Miscellaneous

- *(deps)* Lock file maintenance ([#37](https://github.com/jdx/expr.rs/pull/37))
- *(deps)* Update rust crate indexmap to v2.14.0 ([#38](https://github.com/jdx/expr.rs/pull/38))
- *(deps)* Lock file maintenance ([#39](https://github.com/jdx/expr.rs/pull/39))
- *(deps)* Lock file maintenance ([#40](https://github.com/jdx/expr.rs/pull/40))
- *(deps)* Lock file maintenance ([#41](https://github.com/jdx/expr.rs/pull/41))
- Set dev profile debug to 1 ([#42](https://github.com/jdx/expr.rs/pull/42))
- *(deps)* Lock file maintenance ([#44](https://github.com/jdx/expr.rs/pull/44))
- *(deps)* Lock file maintenance ([#45](https://github.com/jdx/expr.rs/pull/45))
- *(deps)* Lock file maintenance ([#46](https://github.com/jdx/expr.rs/pull/46))
- *(deps)* Lock file maintenance lockfile maintenance ([#49](https://github.com/jdx/expr.rs/pull/49))
- *(deps)* Lock file maintenance lockfile maintenance ([#51](https://github.com/jdx/expr.rs/pull/51))
- *(deps)* Lock file maintenance lockfile maintenance ([#53](https://github.com/jdx/expr.rs/pull/53))
- *(deps)* Lock file maintenance ([#55](https://github.com/jdx/expr.rs/pull/55))
- *(deps)* Lock file maintenance ([#56](https://github.com/jdx/expr.rs/pull/56))
- *(deps)* Update rust crate regex to v1.13.1 ([#60](https://github.com/jdx/expr.rs/pull/60))
- *(deps)* Update rust crate serde_json to v1.0.151 ([#64](https://github.com/jdx/expr.rs/pull/64))
- *(deps)* Update rust crate thiserror to v2.0.19 ([#65](https://github.com/jdx/expr.rs/pull/65))
- *(deps)* Update rust crate serde to v1.0.229 ([#63](https://github.com/jdx/expr.rs/pull/63))
- *(deps)* Update rust crate pest_derive to v2.8.8 ([#67](https://github.com/jdx/expr.rs/pull/67))
- *(deps)* Lock file maintenance ([#68](https://github.com/jdx/expr.rs/pull/68))
- Harden v2 release checks ([#92](https://github.com/jdx/expr.rs/pull/92))

### Performance

- *(lib)* Borrow compiled programs during evaluation ([#75](https://github.com/jdx/expr.rs/pull/75))
- *(parse)* Precompile literal regexes ([#77](https://github.com/jdx/expr.rs/pull/77))

### Refactor

- *(lib)* Rename number value to integer ([#72](https://github.com/jdx/expr.rs/pull/72))

### Testing

- Add go expr compatibility corpus ([#85](https://github.com/jdx/expr.rs/pull/85))

## [1.1.1] - 2026-02-10

### Bug Fixes

- Support braceless predicates matching Go expr-lang behavior ([#23](https://github.com/jdx/expr.rs/pull/23))

## [0.4.0] - 2026-01-25

### 🚀 Features

- Add JSON and utility functions (#18)

### ⚙️ Miscellaneous Tasks

- Add renovate config (#19)
- Add CLAUDE.md for Claude Code guidance
- Update dependencies
## [0.3.2] - 2025-06-16

### 🐛 Bug Fixes

- Parse signs as unary operators (#17)

### ⚙️ Miscellaneous Tasks

- Release expr-lang version 0.3.2
## [0.3.1] - 2025-06-15

### 🐛 Bug Fixes

- Correct operator precedences to match with go implementation (#16)

### ⚙️ Miscellaneous Tasks

- Release expr-lang version 0.3.1
## [0.3.0] - 2025-03-18

### ⚙️ Miscellaneous Tasks

- Strum 0.27
- Release expr-lang version 0.3.0
## [0.2.2] - 2025-01-05

### 🐛 Bug Fixes

- Add "and" and "or" for logical operator

### ⚙️ Miscellaneous Tasks

- Release expr-lang version 0.2.2
## [0.2.1] - 2024-11-29

### ⚙️ Miscellaneous Tasks

- Release expr-lang version 0.2.1
## [0.2.0] - 2024-11-29

### ⚙️ Miscellaneous Tasks

- Release expr-lang version 0.2.0
## [0.1.6] - 2024-11-25

### 🚀 Features

- Add variables
- Filter func
- String functions
- Array functions
- Array functions

### 🐛 Bug Fixes

- Support $env

### 🧪 Testing

- Refactor

### ⚙️ Miscellaneous Tasks

- Release expr-lang version 0.1.6
## [0.1.5] - 2024-11-25

### 🐛 Bug Fixes

- Better support for functions

### ⚙️ Miscellaneous Tasks

- Release expr-lang version 0.1.5
## [0.1.4] - 2024-11-24

### 🐛 Bug Fixes

- Prep

### ⚙️ Miscellaneous Tasks

- Release expr-lang version 0.1.4
## [0.1.3] - 2024-11-24

### 🐛 Bug Fixes

- Make ExprProgram cloneable

### ⚙️ Miscellaneous Tasks

- Release expr-lang version 0.1.3
## [0.1.2] - 2024-11-24

### 🚀 Features

- Added value helpers

### 🐛 Bug Fixes

- Added Debug and Clone to parser
- String escaping

### ⚙️ Miscellaneous Tasks

- Release expr-lang version 0.1.2
## [0.1.1] - 2024-11-24

### 🐛 Bug Fixes

- Context

### ⚙️ Miscellaneous Tasks

- Changelog
- Set use_cargo_conventions
- Release expr-lang version 0.1.1
## [0.1.0] - 2024-11-24
