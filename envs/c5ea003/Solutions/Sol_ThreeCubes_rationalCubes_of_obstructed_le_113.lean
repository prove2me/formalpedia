-- Prove2me | solution 1 for ThreeCubes.rationalCubes_of_obstructed_le_113
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:01:04.158504+00:00
-- url     : https://prove2.me/submissions/962abca7-43c6-4352-95a9-f185ca30642a

-- Sol generated from Probability/Rational.lean
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

















open ThreeCubes in
theorem solution(n : ℤ) (h0 : 0 ≤ n) (h1 : n ≤ 113)
    (hm : n % 9 = 4 ∨ n % 9 = 5) : IsSumOfThreeRationalCubes (n : ℚ) := by
  have hcase : n = 4 ∨ n = 5 ∨ n = 13 ∨ n = 14 ∨ n = 22 ∨ n = 23 ∨ n = 31 ∨ n = 32 ∨
      n = 40 ∨ n = 41 ∨ n = 49 ∨ n = 50 ∨ n = 58 ∨ n = 59 ∨ n = 67 ∨ n = 68 ∨ n = 76 ∨
      n = 77 ∨ n = 85 ∨ n = 86 ∨ n = 94 ∨ n = 95 ∨ n = 103 ∨ n = 104 ∨ n = 112 ∨
      n = 113 := by omega
  rcases hcase with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h <;> subst h
  · exact ⟨-23, 121 / 6, 95 / 6, by norm_num⟩
  · exact ⟨-2, 7 / 3, 2 / 3, by norm_num⟩
  · exact ⟨0, 7 / 3, 2 / 3, by norm_num⟩
  · exact ⟨2 / 3, 7 / 3, 1, by norm_num⟩
  · exact ⟨-3, 11 / 3, -2 / 3, by norm_num⟩
  · exact ⟨1 / 2, 7 / 3, 13 / 6, by norm_num⟩
  · exact ⟨-6, 20 / 3, -11 / 3, by norm_num⟩
  · exact ⟨-46, 121 / 3, 95 / 3, by norm_num⟩
  · exact ⟨2 / 3, 3, 7 / 3, by norm_num⟩
  · exact ⟨-2, 11 / 3, -2 / 3, by norm_num⟩
  · exact ⟨-2 / 3, 11 / 3, 0, by norm_num⟩
  · exact ⟨-2 / 3, 11 / 3, 1, by norm_num⟩
  · exact ⟨-5, 14 / 3, 13 / 3, by norm_num⟩
  · exact ⟨-3, 13 / 3, 5 / 3, by norm_num⟩
  · exact ⟨-8, 25 / 3, 2 / 3, by norm_num⟩
  · exact ⟨11 / 6, 7 / 2, 8 / 3, by norm_num⟩
  · exact ⟨-2 / 3, 11 / 3, 3, by norm_num⟩
  · exact ⟨2 / 3, 4, 7 / 3, by norm_num⟩
  · exact ⟨-1, 13 / 3, 5 / 3, by norm_num⟩
  · exact ⟨0, 13 / 3, 5 / 3, by norm_num⟩
  · exact ⟨5 / 3, 13 / 3, 2, by norm_num⟩
  · exact ⟨-8, 29 / 3, -20 / 3, by norm_num⟩
  · exact ⟨-1, 14 / 3, 4 / 3, by norm_num⟩
  · exact ⟨0, 14 / 3, 4 / 3, by norm_num⟩
  · exact ⟨4 / 3, 14 / 3, 2, by norm_num⟩
  · exact ⟨-2 / 3, 4, 11 / 3, by norm_num⟩
