-- Prove2me | Definitions.Def_Bridges_FibonacciPythagorean
-- name    : Bridges_FibonacciPythagorean
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:20:25.36161+00:00
-- url     : https://prove2.me/theorems/22f21107-eb68-4a71-b4e4-39eb5da24c17
-- title:
--   Aether Catalog definitions — Bridges_FibonacciPythagorean
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.FibonacciPythagorean`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/FibonacciPythagorean.lean by skeleton subtraction
import Mathlib

/-!
# A Fibonacci–Pythagorean bridge

This file connects two catalog domains — the Fibonacci / number-theory world and the
Pythagorean / plane-geometry world — through the classical construction that turns four
consecutive Fibonacci numbers into a right triangle.

Given consecutive Fibonacci numbers `F n, F (n+1), F (n+2), F (n+3)`, the pair of legs

* `A = F n · F (n+3)`  (product of the outer two), and
* `B = 2 · F (n+1) · F (n+2)`  (twice the product of the inner two)

together with the hypotenuse `C = F (n+1)² + F (n+2)²` form a Pythagorean triple, and the
hypotenuse is itself the Fibonacci number `F (2n+3)`.  For `n = 2` this reproduces the
smallest triple `(3, 4, 5)`; for `n = 3`, `(5, 12, 13)`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The Raine/Horadam construction should give an *exact*
Pythagorean identity for every `n`, and its hypotenuse should coincide with the Fibonacci
number `F (2n+3)` via the addition formula `F (m+n+1) = F m F n + F (m+1) F (n+1)`.

Experiment (Experimenter): Reduced `A² + B² = C²` to a two-variable polynomial identity in
`x = F n`, `y = F (n+1)` after expanding `F (n+2)`, `F (n+3)` by the recurrence; closed by
`ring`.  Identified `C = F (2n+3)` as the `m = n = n+1` case of `Nat.fib_add`.

Analysis (Analyst): The construction is a *polynomial* identity, so it needs no induction
beyond the recurrence unfolding — the depth lives in matching the algebra to `Nat.fib_add`.
The triples are not always primitive (e.g. `n = 4` gives `(16,30,34) = 2·(8,15,17)`), so no
primitivity claim is made.

Critique (Critic): Verified non-degeneracy — for `n ≥ 1` both legs are strictly positive,
so the triangle is genuine, ruling out a vacuous "triple" with a zero leg.

Synthesis (PI): One recurrence expansion + one addition-formula application bridge the
Fibonacci recurrence to Euclidean right triangles, with `F (2n+3)` as the hypotenuse.
-- !-- Lab Notes -- !--
-/

namespace FibonacciPythagorean

open Nat

/-- The two legs of the Fibonacci right triangle at index `n`. -/
def legA (n : ℕ) : ℕ := Nat.fib n * Nat.fib (n + 3)

/-- The second leg (twice the product of the inner two Fibonacci numbers). -/
def legB (n : ℕ) : ℕ := 2 * Nat.fib (n + 1) * Nat.fib (n + 2)

/-- The hypotenuse, as a sum of two squares of Fibonacci numbers. -/
def hyp (n : ℕ) : ℕ := Nat.fib (n + 1) ^ 2 + Nat.fib (n + 2) ^ 2

/-
**Pythagorean identity.**  `A² + B² = C²`.
-/

/-
**The hypotenuse is a Fibonacci number:** `C = F (2n+3)`.
-/

/-
**Fibonacci–Pythagorean triple.**  The legs `A`, `B` and the Fibonacci hypotenuse
`F (2n+3)` satisfy the Pythagorean relation.
-/

/-
**Non-degeneracy:** for `n ≥ 1` both legs are strictly positive, so the triangle is
genuine.
-/

end FibonacciPythagorean


