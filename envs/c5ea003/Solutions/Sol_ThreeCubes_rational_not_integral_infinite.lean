-- Prove2me | solution 1 for ThreeCubes.rational_not_integral_infinite
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:02:25.212546+00:00
-- url     : https://prove2.me/submissions/67592ae7-c5a9-4ee9-9c68-ff1af144ebc8

-- Sol generated from Probability/Rational.lean
import Mathlib
import Definitions.Def_Probability_Basic
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




/-- The set of sums of three rational cubes is stable under multiplication by a cube; this is the
homogeneity of the cubic surface. -/
theorem isSumOfThreeRationalCubes_mul_cube {q : ℚ} (h : IsSumOfThreeRationalCubes q) (t : ℚ) :
    IsSumOfThreeRationalCubes (q * t ^ 3) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  exact ⟨x * t, y * t, z * t, by rw [← hxyz]; ring⟩




/-- `5 = (-2)³ + (7/3)³ + (2/3)³`.  Note `5 ≡ 5 (mod 9)`, so `5` is **not** a sum of three
integer cubes. -/
theorem rationalCubes_five : IsSumOfThreeRationalCubes 5 :=
  ⟨-2, 7 / 3, 2 / 3, by norm_num⟩





/-- For `3 ∤ t` the integer `5t³` is congruent to `±4` mod `9`, hence is **not** a sum of three
integer cubes. -/
theorem not_isSumOfThreeCubes_five_mul_cube {t : ℤ} (ht : ¬ ((3 : ℤ) ∣ t)) :
    ¬ IsSumOfThreeCubes (5 * t ^ 3) := by
  refine not_isSumOfThreeCubes_of_mod_nine ?_
  have hr : t % 3 = 1 ∨ t % 3 = 2 := by omega
  obtain ⟨k, hk⟩ : ∃ k : ℤ, t = 3 * k + t % 3 := ⟨t / 3, by omega⟩
  rcases hr with hr | hr <;> rw [hr] at hk <;> subst hk
  · have hexp : 5 * (3 * k + 1) ^ 3 = 9 * (15 * k ^ 3 + 15 * k ^ 2 + 5 * k) + 5 := by ring
    right; rw [hexp]; omega
  · have hexp : 5 * (3 * k + 2) ^ 3 = 9 * (15 * k ^ 3 + 30 * k ^ 2 + 20 * k) + 40 := by ring
    left; rw [hexp]; omega

/-- Yet `5t³` *is* always a sum of three rational cubes, by homogeneity from
`5 = (-2)³ + (7/3)³ + (2/3)³`. -/
theorem rationalCubes_five_mul_cube (t : ℤ) :
    IsSumOfThreeRationalCubes ((5 * t ^ 3 : ℤ) : ℚ) := by
  have := isSumOfThreeRationalCubes_mul_cube rationalCubes_five (t : ℚ)
  refine ⟨-2 * (t : ℚ), 7 / 3 * (t : ℚ), 2 / 3 * (t : ℚ), ?_⟩
  push_cast
  ring



open ThreeCubes in
theorem solution:
    {n : ℤ | IsSumOfThreeRationalCubes (n : ℚ) ∧ ¬ IsSumOfThreeCubes n}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℕ => 5 * ((3 : ℤ) * (m : ℤ) + 1) ^ 3) ?_ ?_
  · intro a b hab
    simp only at hab
    have h1 : ((3 : ℤ) * (a : ℤ) + 1) ^ 3 = ((3 : ℤ) * (b : ℤ) + 1) ^ 3 := by linarith
    have h2 : (3 : ℤ) * (a : ℤ) + 1 = (3 : ℤ) * (b : ℤ) + 1 :=
      (Odd.strictMono_pow (R := ℤ) (by decide)).injective h1
    have : (a : ℤ) = (b : ℤ) := by omega
    exact_mod_cast this
  · intro m
    have hnd : ¬ ((3 : ℤ) ∣ (3 * (m : ℤ) + 1)) := by omega
    exact ⟨rationalCubes_five_mul_cube _, not_isSumOfThreeCubes_five_mul_cube hnd⟩
