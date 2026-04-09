# NUMEX Lang

NUMEX is a small, dynamically-typed interpreted programming language implemented in [Racket](https://racket-lang.org/). It was built as a Programming Languages course project and demonstrates core concepts of language implementation: expression evaluation under an environment, first-class functions with lexical scoping, recursive closures, pairs, lists, and an optional challenge extension that computes free variables to build minimal closures.

---

## Table of Contents

- [Features](#features)
- [Language Reference](#language-reference)
  - [Values](#values)
  - [Arithmetic](#arithmetic)
  - [Logical Operations](#logical-operations)
  - [Comparison & Branching](#comparison--branching)
  - [Variables & Binding](#variables--binding)
  - [Functions & Application](#functions--application)
  - [Pairs & Lists](#pairs--lists)
  - [Built-in Higher-Order Functions](#built-in-higher-order-functions)
- [Challenge Extension](#challenge-extension)
- [Project Structure](#project-structure)
- [Getting Started](#getting-started)
- [Running Tests](#running-tests)
- [Examples](#examples)

---

## Features

- **Arithmetic** – integer addition, subtraction, multiplication, integer division, and negation.
- **Boolean logic** – short-circuit `andalso` / `orelse`, boolean negation, and equality testing.
- **Conditionals** – `cnd`, `ifnzero`, `ifleq`, `ifneq`, `ifmunit`.
- **First-class functions** – named recursive lambdas (`lam`) with lexical scoping via closures.
- **Pairs & linked lists** – `apair`, `1st`, `2nd`, `munit` (empty / unit value), plus conversion helpers between NUMEX lists and Racket lists.
- **Higher-order functions** – `numex-filter` and `numex-all-gt` defined entirely inside the NUMEX language.
- **Challenge extension** – `compute-free-vars` for static free-variable analysis and `eval-exp-c` for building minimal closures that capture only the variables they actually need.

---

## Language Reference

### Values

| Constructor | Racket syntax | Description |
|---|---|---|
| Integer | `(num 42)` | A whole-number constant. Floats are rejected. |
| Boolean | `(bool #t)` / `(bool #f)` | A boolean constant. |
| Unit | `(munit)` | The unit value; also used as the empty-list sentinel. |
| Closure | produced by `lam` evaluation | A first-class function value. |
| Pair | `(apair e1 e2)` | An evaluated pair of two values. |

### Arithmetic

| Expression | Description |
|---|---|
| `(plus e1 e2)` | `e1 + e2` — both operands must be integers. |
| `(minus e1 e2)` | `e1 - e2` — both operands must be integers. |
| `(mult e1 e2)` | `e1 * e2` — both operands must be integers. |
| `(div e1 e2)` | Integer quotient `e1 / e2`; raises an error if `e2 = 0`. |
| `(neg e)` | Arithmetic negation when `e` is an integer; logical NOT when `e` is a boolean. |

### Logical Operations

| Expression | Description |
|---|---|
| `(andalso e1 e2)` | Short-circuit AND. Returns `(bool #f)` without evaluating `e2` if `e1` is false. |
| `(orelse e1 e2)` | Short-circuit OR. Returns `(bool #t)` without evaluating `e2` if `e1` is true. |
| `(iseq e1 e2)` | Deep equality check. Returns `(bool #t)` if both operands are equal integers or equal booleans; `(bool #f)` otherwise (no error on mixed types). |

### Comparison & Branching

| Expression | Description |
|---|---|
| `(cnd e1 e2 e3)` | If `e1` evaluates to `(bool #t)`, returns `e2`; else returns `e3`. `e1` must be a boolean. |
| `(ifnzero e1 e2 e3)` | If integer `e1 ≠ 0`, returns `e2`; else `e3`. |
| `(ifleq e1 e2 e3 e4)` | If integer `e1 ≤ e2`, returns `e3`; else `e4`. |
| `(ifneq e1 e2 e3 e4)` | If `e1 ≠ e2`, returns `e3`; else `e4`. (Macro built on `iseq`.) |
| `(ifmunit e1 e2 e3)` | If `e1` is `(munit)`, returns `e2`; else `e3`. (Macro.) |
| `(ismunit e)` | Returns `(bool #t)` if `e` evaluates to `(munit)`. |
| `(isnumexlist e)` | Returns `(bool #t)` if `e` is a proper NUMEX list (chain of `apair` ending in `munit`). |

### Variables & Binding

| Expression | Description |
|---|---|
| `(var "x")` | Look up variable `"x"` in the current environment. Raises an error if unbound. |
| `(with "x" e1 e2)` | Bind `"x"` to the value of `e1` and evaluate `e2` in the extended environment. |
| `(with* bindings e)` | Sequential `let*`-style binding. `bindings` is a Racket list of `(cons name expr)` pairs. |

### Functions & Application

| Expression | Description |
|---|---|
| `(lam nameopt formal body)` | Creates a lambda. `nameopt` is either a string (enabling recursion by self-reference) or `null` (anonymous). `formal` is the parameter name string. Evaluates to a `closure`. |
| `(apply funexp actual)` | Apply the closure produced by `funexp` to the value of `actual`. |

### Pairs & Lists

| Expression / Helper | Description |
|---|---|
| `(apair e1 e2)` | Construct a pair from two expressions. |
| `(1st e)` | Extract the first element of a pair. |
| `(2nd e)` | Extract the second element of a pair. |
| `(racketlist->numexlist lst)` | Convert a Racket list to a NUMEX linked list (`apair` chain ending with `munit`). |
| `(numexlist->racketlist lst)` | Convert a NUMEX list back to a Racket list. |

---

## Built-in Higher-Order Functions

These are NUMEX values defined in `project.rkt` using only NUMEX constructs.

### `numex-filter`

`numex-filter` takes a unary function `f` and a NUMEX list, and returns a new list containing only those elements `x` for which `(f x)` is non-zero.

```racket
; Keep only elements greater than 5
(eval-exp
  (apply (apply numex-all-gt (num 5))
         (racketlist->numexlist (list (num 10) (num 4) (num 15)))))
; => (apair (num 10) (apair (num 15) (munit)))
```

### `numex-all-gt`

`numex-all-gt` takes a threshold integer `i` and a NUMEX list, and returns only the elements strictly greater than `i`. It is built on top of `numex-filter`.

```racket
(eval-exp
  (apply (apply numex-all-gt (num 5))
         (racketlist->numexlist (list (num 10) (num 4) (num 5) (num 15)))))
; => (apair (num 10) (apair (num 15) (munit)))
```

---

## Challenge Extension

Two additional features provide optimised closure creation:

### `compute-free-vars`

```racket
(compute-free-vars e)
```

Traverses a NUMEX expression `e` and transforms every `lam` into a `fun-challenge` struct annotated with the **set of free variables** in its body. This information is later used to build minimal closures.

### `eval-exp-c`

```racket
(eval-exp-c e)
```

An alternative evaluator that uses `compute-free-vars` to capture **only the free variables** of a function in its closure, rather than the entire ambient environment. This reduces memory use and makes closure environments predictable.

```racket
; Only "x" is free; "w" is not captured
(closure-env
  (eval-exp-c
    (with* (list (cons "w" (num 3)) (cons "x" (num 1)) (cons "y" (num 2)))
           (lam "f" "y" (plus (var "x") (var "y"))))))
; => (list (cons "x" (num 1)))
```

---

## Project Structure

```
NUMEX-Lang/
├── project.rkt          # Language implementation (structs, evaluator, stdlib)
├── TestCases.rkt        # Standard test suite (131 tests, scored out of 100)
├── CtestCases.rkt       # Challenge test suite (free-vars & eval-exp-c tests)
├── grade.txt            # Score written by TestCases.rkt after a run
├── grade-Challenging.txt# Score written by CtestCases.rkt after a run
└── README.md
```

---

## Getting Started

### Prerequisites

- [Racket](https://racket-lang.org/) 7.x or later.

### Installation

```bash
git clone https://github.com/mahi97/NUMEX-Lang.git
cd NUMEX-Lang
```

No additional packages are required; the project uses only the standard Racket distribution.

---

## Running Tests

Run the standard test suite (writes score to `grade.txt`):

```bash
racket TestCases.rkt
```

Run the challenge test suite (writes score to `grade-Challenging.txt`):

```bash
racket CtestCases.rkt
```

Both test runners print a summary to the terminal and write a detailed log to their respective output files.

---

## Examples

```racket
#lang racket
(require "project.rkt")

;; Arithmetic
(eval-exp (plus (num 3) (mult (num 4) (num 5))))   ; => (num 23)
(eval-exp (div  (num 10) (num 3)))                 ; => (num 3)  (integer division)

;; Booleans & logic
(eval-exp (andalso (bool #t) (bool #f)))           ; => (bool #f)
(eval-exp (neg (bool #t)))                         ; => (bool #f)

;; Variables & binding
(eval-exp (with "x" (num 7) (plus (var "x") (num 1)))) ; => (num 8)

;; Recursive factorial
(eval-exp
  (apply
    (lam "fact" "n"
         (cnd (iseq (var "n") (num 0))
              (num 1)
              (mult (var "n") (apply (var "fact") (minus (var "n") (num 1))))))
    (num 5)))
; => (num 120)

;; Pairs & lists
(eval-exp (1st (apair (num 42) (bool #t))))        ; => (num 42)

(numexlist->racketlist
  (eval-exp
    (apply (apply numex-all-gt (num 3))
           (racketlist->numexlist (list (num 1) (num 4) (num 2) (num 5))))))
; => (list (num 4) (num 5))
```
