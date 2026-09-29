-- Prove2me | Theorems.Thm_ThreeCubes_rationalCubes_window
-- name    : ThreeCubes.rationalCubes_window
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:14:20.214027+00:00
-- url     : https://prove2.me/theorems/2e32ba5e-0751-4618-961a-a730b084a1f3
-- title:
--   Every integer with `|n| ≤ 113` is a sum of three rational cubes.
-- statement:
--   **Every integer with `|n| ≤ 113` is a sum of three rational cubes.**
--
--   For `n ≢ ±4 (mod 9)` this follows from the integral verification `hasse_of_abs_le_113`; for the
--   `52` obstructed values (`±4, ±5, ±13, …, ±113`) genuinely rational witnesses are needed, and are
--   supplied by `rationalCubes_of_obstructed_le_113`.  Thus in the entire window that is currently
--   verifiable, the rational problem is unobstructed while the integral one is not.
--
--   ```lean
--   theorem ThreeCubes.rationalCubes_window(n : ℤ) (h : |n| ≤ 113) : IsSumOfThreeRationalCubes (n : ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/Rational.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/Rational.lean#L126

-- Thm stub generated from Probability/Rational.lean
import Mathlib
import Definitions.Def_Probability_Rational
import Definitions.Def_Probability_Witnesses

/-!
# The mod `9` obstruction is *purely integral*: sums of three **rational** cubes

Over `ℤ` the congruence `n ≡ ±4 (mod 9)` is a genuine obstruction to `x³+y³+z³ = n`
(`ThreeCubes.not_isSumOfThreeCubes_of_mod_nine`), and by `ThreeCubes.locallySolvable_iff` it is the
*only* local obstruction.  This file shows that the obstruction evaporates completely as soon as
one allows **rational** cubes.  Concretely:

* `sum_two_rational_cubes_form` — the classical parametrisation of sums of two rational cubes:
  `a(a²+3b²)/4 = ((a+b)/2)³ + ((a-b)/2)³`.
* `rationalCubes_five`, `rationalCubes_four` — the two smallest obstructed integers are sums of
  three rational cubes, e.g. `5 = (-2)³ + (7/3)³ + (2/3)³` and
  `4 = (-23)³ + (121/6)³ + (95/6)³`.
* `rationalCubes_of_obstructed_le_113` — explicit rational representations of *all* `26`
  integers `0 ≤ n ≤ 113` with `n ≡ ±4 (mod 9)`; every one of them has denominator `3` or `6`.
* `rationalCubes_window` — combining this with `hasse_of_abs_le_113`: **every** integer with
  `|n| ≤ 113` is a sum of three rational cubes.  So in the whole verified window the rational
  problem has no obstruction whatsoever, in sharp contrast with the integral one.
* `denominator_three_dvd_of_obstructed` — the flip side: any rational representation of an
  obstructed `n` must have denominators divisible by `3`, which is exactly why the integral
  obstruction is invisible over `ℚ`.
* `rational_not_integral_infinite` — there are infinitely many integers that are sums of three
  rational cubes but not of three integer cubes (`5t³` for `3 ∤ t`).
-/

open ThreeCubes

theorem ThreeCubes.rationalCubes_window(n : ℤ) (h : |n| ≤ 113) : IsSumOfThreeRationalCubes (n : ℚ) := by sorry
