-- Prove2me | Theorems.Thm_ThreeCubes_denominator_three_dvd_of_obstructed
-- name    : ThreeCubes.denominator_three_dvd_of_obstructed
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:12:28.907604+00:00
-- url     : https://prove2.me/theorems/9a6224b9-8273-4731-bed3-c59c92488b22
-- title:
--   The denominators are forced.
-- statement:
--   **The denominators are forced.**  If `n ≡ ±4 (mod 9)` and `n = x³+y³+z³` with `x, y, z`
--   rational sharing the common denominator `d`, then `3 ∣ d`.  Indeed otherwise
--   `X³+Y³+Z³ = n d³` would be an integral representation of an integer `≡ ±4 (mod 9)`.  This
--   explains why every witness above has denominator a multiple of `3`.
--
--   ```lean
--   theorem ThreeCubes.denominator_three_dvd_of_obstructed{n : ℤ} (hn : n % 9 = 4 ∨ n % 9 = 5)
--       {d X Y Z : ℤ} (h : X ^ 3 + Y ^ 3 + Z ^ 3 = n * d ^ 3) : (3 : ℤ) ∣ d := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/Rational.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/Rational.lean#L150

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

theorem ThreeCubes.denominator_three_dvd_of_obstructed{n : ℤ} (hn : n % 9 = 4 ∨ n % 9 = 5)
    {d X Y Z : ℤ} (h : X ^ 3 + Y ^ 3 + Z ^ 3 = n * d ^ 3) : (3 : ℤ) ∣ d := by sorry
