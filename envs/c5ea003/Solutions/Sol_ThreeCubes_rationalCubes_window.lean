-- Prove2me | solution 1 for ThreeCubes.rationalCubes_window
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:02:24.623157+00:00
-- url     : https://prove2.me/submissions/2e5ada3b-362a-4a2e-a240-9889ba2d56c6

-- Sol generated from Probability/Rational.lean
import Mathlib
import Definitions.Def_Probability_Basic
import Definitions.Def_Probability_Rational
import Definitions.Def_Probability_Witnesses
import Theorems.Thm_ThreeCubes_hasse_of_abs_le_113
import Theorems.Thm_ThreeCubes_locallySolvable_of_not_mod_nine
import Theorems.Thm_ThreeCubes_rationalCubes_of_obstructed_le_113

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


/-- An integral representation is in particular a rational one. -/
theorem isSumOfThreeRationalCubes_of_int {n : ℤ} (h : IsSumOfThreeCubes n) :
    IsSumOfThreeRationalCubes (n : ℚ) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  refine ⟨(x : ℚ), (y : ℚ), (z : ℚ), ?_⟩
  exact_mod_cast congrArg (fun m : ℤ => (m : ℚ)) hxyz

/-- The set of sums of three rational cubes is stable under negation. -/
theorem isSumOfThreeRationalCubes_neg {q : ℚ} (h : IsSumOfThreeRationalCubes q) :
    IsSumOfThreeRationalCubes (-q) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  exact ⟨-x, -y, -z, by rw [← hxyz]; ring⟩














open ThreeCubes in
theorem solution(n : ℤ) (h : |n| ≤ 113) : IsSumOfThreeRationalCubes (n : ℚ) := by
  rw [abs_le] at h
  obtain ⟨hlo, hhi⟩ := h
  -- reduce to `0 ≤ n`
  have key : ∀ m : ℤ, 0 ≤ m → m ≤ 113 → IsSumOfThreeRationalCubes (m : ℚ) := by
    intro m hm0 hm1
    by_cases hobs : m % 9 = 4 ∨ m % 9 = 5
    · exact rationalCubes_of_obstructed_le_113 m hm0 hm1 hobs
    · push_neg at hobs
      exact isSumOfThreeRationalCubes_of_int
        (hasse_of_abs_le_113 m (by rw [abs_le]; omega)
          (locallySolvable_of_not_mod_nine hobs.1 hobs.2))
  by_cases hn : 0 ≤ n
  · exact key n hn hhi
  · push_neg at hn
    have := isSumOfThreeRationalCubes_neg (key (-n) (by omega) (by omega))
    simpa using this
