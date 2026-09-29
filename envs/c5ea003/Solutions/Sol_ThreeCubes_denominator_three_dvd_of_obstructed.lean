-- Prove2me | solution 1 for ThreeCubes.denominator_three_dvd_of_obstructed
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:45:32.879173+00:00
-- url     : https://prove2.me/submissions/bf66c51a-ad67-4b8e-806a-211bc6982727

-- Sol generated from Probability/Rational.lean
import Mathlib
import Definitions.Def_Probability_Rational
import Definitions.Def_Probability_Witnesses
import Theorems.Thm_ThreeCubes_not_isSumOfThreeCubes_of_mod_nine

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

















open ThreeCubes in
theorem solution{n : ℤ} (hn : n % 9 = 4 ∨ n % 9 = 5)
    {d X Y Z : ℤ} (h : X ^ 3 + Y ^ 3 + Z ^ 3 = n * d ^ 3) : (3 : ℤ) ∣ d := by
  by_contra hdiv
  -- `d³ ≡ ±1 (mod 9)`, hence `n d³ ≡ ±4 (mod 9)`, contradicting the integral obstruction.
  have hr : d % 3 = 1 ∨ d % 3 = 2 := by omega
  have hkey : (n * d ^ 3) % 9 = 4 ∨ (n * d ^ 3) % 9 = 5 := by
    obtain ⟨k, hk⟩ : ∃ k : ℤ, d = 3 * k + d % 3 := ⟨d / 3, by omega⟩
    rcases hr with hr | hr <;> rw [hr] at hk <;> subst hk
    · have hexp : n * (3 * k + 1) ^ 3 =
          9 * (n * (3 * k ^ 3 + 3 * k ^ 2 + k)) + n := by ring
      rw [hexp]; omega
    · have hexp : n * (3 * k + 2) ^ 3 =
          9 * (n * (3 * k ^ 3 + 6 * k ^ 2 + 4 * k)) + 8 * n := by ring
      rw [hexp]; omega
  exact not_isSumOfThreeCubes_of_mod_nine hkey ⟨X, Y, Z, h⟩
