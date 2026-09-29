-- Prove2me | Definitions.Def_Novelty_MandelbrotFareyFibonacci
-- name    : Novelty_MandelbrotFareyFibonacci
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:32:27.745624+00:00
-- url     : https://prove2.me/theorems/70449643-19dc-4b13-a477-44e768da6a65
-- title:
--   Aether Catalog definitions — Novelty_MandelbrotFareyFibonacci
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.MandelbrotFareyFibonacci`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/MandelbrotFareyFibonacci.lean by skeleton subtraction
import Mathlib

/-!
# Farey Mediants, Fibonacci, and the Bulb Ordering of the Mandelbrot Set

Along the boundary of the main cardioid of the Mandelbrot set, the periods of the attached bulbs
are organised by the **Farey/Stern–Brocot** structure of their external angles `p/q`: two bulbs
`p/q` and `p'/q'` are *adjacent* exactly when `|p q' - p' q| = 1` (the unimodular / Farey-neighbour
condition), and the bulb sitting between them carries the **mediant** angle
`(p + p')/(q + q')`.

The distinguished "golden" path — following the largest satellite bulb at each stage — realises the
**Fibonacci sequence** as iterated mediants:
`1/1, 1/2, 2/3, 3/5, 5/8, …` are the ratios `F n / F (n+1)`.

This file proves:

* `fib_mediant`: the mediant of the consecutive Fibonacci ratios `F n / F (n+1)` and
  `F (n+1) / F (n+2)` is the next one, `F (n+2) / F (n+3)`;
* `fib_cassini`: Cassini's identity `F(n+1)² - F n · F(n+2) = (-1)ⁿ`, i.e. consecutive Fibonacci
  ratios are **Farey neighbours** (unimodular);
* `fib_farey_neighbor`: the resulting `|·| = 1` unimodularity statement;
* `fib_coprime`: consecutive Fibonacci numbers are coprime, so the ratios are in lowest terms.
-/

namespace FareyFibonacci

/-- The mediant of two fractions given as `(numerator, denominator)` pairs. -/
def mediant (a b : ℕ × ℕ) : ℕ × ℕ := (a.1 + b.1, a.2 + b.2)

/-
**Fibonacci as iterated mediants.**  The mediant of the consecutive Fibonacci ratios
`F n / F (n+1)` and `F (n+1) / F (n+2)` is the next Fibonacci ratio `F (n+2) / F (n+3)`.
-/

/-
**Cassini's identity.**  `F(n+1)² - F n · F(n+2) = (-1)ⁿ`.
-/

/-
**Farey-neighbour / unimodularity.**  Consecutive Fibonacci ratios `F n / F(n+1)` and
`F(n+1) / F(n+2)` are Farey neighbours: the determinant has absolute value `1`.
-/

/-
Consecutive Fibonacci numbers are coprime, so each mediant ratio `F n / F(n+1)` is already in
lowest terms.
-/

/-
The denominators of the golden path strictly increase (`F (n+1) < F (n+2)` for `n ≥ 1`), so the
bulbs it visits shrink — the size of the `p/q` bulb decreases with `q`.
-/

end FareyFibonacci


