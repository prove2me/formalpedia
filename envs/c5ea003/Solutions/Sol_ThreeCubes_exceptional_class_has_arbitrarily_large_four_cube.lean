-- Prove2me | solution 1 for ThreeCubes.exceptional_class_has_arbitrarily_large_four_cube
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:56:10.965245+00:00
-- url     : https://prove2.me/submissions/69b810a4-f236-438d-938c-c82ac3f30af6

-- Sol generated from Probability/FourCubesExtended.lean
import Mathlib
import Definitions.Def_Probability_FourCubes

/-!
# Four cubes: closing the `±2, ±16 (mod 54)` gap down to six classes mod `216`

`Probability.ThreeCubes.FourCubes` proves that every integer `n` with `n ≢ ±4 (mod 9)` and
`n ≢ ±2, ±16 (mod 54)` is a sum of four integer cubes: `38` of the `54` classes mod `54`,
equivalently `152` of the `216` classes mod `216`.

This file pushes the covering further.  Six new one-parameter linear families — two of modulus
`72`, two of modulus `108` and two of modulus `216` — fill in ten of the sixteen residue classes
modulo `216` that were previously missed, leaving only

`n ≡ ±38, ±52, ±70 (mod 216)`

uncovered among the classes with `n ≢ ±4 (mod 9)`.  So `162` of the `168` admissible classes
modulo `216` are now certified.

The families were produced by the same mechanism as in `FourCubes`: a quadruple `(aᵢ)` with
`∑ aᵢ³ = 0` together with a shift `(bᵢ)` with `∑ aᵢ²bᵢ = 0` makes

`∑ (aᵢ k + bᵢ)³ = 3(∑ aᵢbᵢ²) k + ∑ bᵢ³`

a *linear* polynomial in `k`; one then needs the slope `3 ∑ aᵢbᵢ²` to be the desired modulus and
the constant `∑ bᵢ³` to be the desired residue.  An exhaustive search over `|aᵢ| ≤ 20`,
`|bᵢ| ≤ 50` found *no* linear family at all whose modulus divides `216` and whose constant lies
in `{±38, ±52, ±70} (mod 216)`; these six classes are therefore beyond the reach of the linear
method, and closing them requires genuinely different (e.g. quadratic) parametrisations.

Main results.

* `ThreeCubes.isSumOfFourCubes_of_mod_seventytwo`,
  `ThreeCubes.isSumOfFourCubes_of_mod_hundredeight`,
  `ThreeCubes.isSumOfFourCubes_of_mod_216_ninetytwo` — the three new covering steps.
* `ThreeCubes.isSumOfFourCubes_of_not_exceptional_216` — the combined statement: every `n`
  with `n ≢ ±4 (mod 9)` and `n % 216 ∉ {38, 52, 70, 146, 164, 178}` is a sum of four cubes.
* The six residues that remain uncovered all satisfy `n ≡ ±2 (mod 9)`; every other admissible
  class modulo `216` is now certified.
* `ThreeCubes.four_cubes_quadratic_family` and
  `ThreeCubes.exceptional_class_has_arbitrarily_large_four_cube` — a *quadratic* mechanism
  `(x+6s)³ + (x-6s)³ + u³ + u³ = 2(x³+u³) + 216xs²` shows that each of the six leftover classes
  still contains arbitrarily large sums of four cubes, so nothing arithmetic obstructs them.
-/

open ThreeCubes

/-! ### Two families of modulus `72` -/



/-! ### Two families of modulus `108` -/



/-! ### Two families of modulus `216` -/



/-! ### The new covering steps -/






/-! ### The six remaining classes are not empty of sums of four cubes

The six classes `±38, ±52, ±70 (mod 216)` are beyond the reach of *linear* families, but they
are certainly not obstructed.  A second, genuinely quadratic mechanism reaches them: from
`(x + w)³ + (x - w)³ = 2x³ + 6xw²` with `w = 6s` one gets

`(x + 6s)³ + (x - 6s)³ + u³ + u³ = 2(x³ + u³) + 216 x s²`,

an arithmetic progression modulo `216` *inside* a quadratic family.  Choosing `(x, u)` with
`2(x³ + u³) ≡ r (mod 216)` therefore produces infinitely many sums of four cubes in the class
`r`, for each of the six exceptional `r`. -/


theorem isSumOfFourCubes_class38 (s : ℤ) : IsSumOfFourCubes (648 * s ^ 2 + 38) :=
  ⟨3 + 6 * s, 3 - 6 * s, -2, -2, by ring⟩

theorem isSumOfFourCubes_class52 (s : ℤ) : IsSumOfFourCubes (648 * s ^ 2 + 52) :=
  ⟨3 + 6 * s, 3 - 6 * s, -1, -1, by ring⟩

theorem isSumOfFourCubes_class70 (s : ℤ) : IsSumOfFourCubes (432 * s ^ 2 + 70) :=
  ⟨2 + 6 * s, 2 - 6 * s, 3, 3, by ring⟩

theorem isSumOfFourCubes_class146 (s : ℤ) : IsSumOfFourCubes (2592 * s ^ 2 + 794) :=
  ⟨12 + 6 * s, 12 - 6 * s, -11, -11, by ring⟩

theorem isSumOfFourCubes_class164 (s : ℤ) : IsSumOfFourCubes (216 * s ^ 2 - 52) :=
  ⟨1 + 6 * s, 1 - 6 * s, -3, -3, by ring⟩

theorem isSumOfFourCubes_class178 (s : ℤ) : IsSumOfFourCubes (432 * s ^ 2 - 38) :=
  ⟨2 + 6 * s, 2 - 6 * s, -3, -3, by ring⟩

/-- A quadratic family with leading coefficient at least `216` and constant term at least `-52`
eventually exceeds any bound, at `s = |M| + 1`. -/
theorem le_quadratic_at_abs_succ {A B M : ℤ} (hA : 216 ≤ A) (hB : -52 ≤ B) :
    M ≤ A * (|M| + 1) ^ 2 + B := by
  set s : ℤ := |M| + 1 with hs
  have hs1 : 1 ≤ s := by have := abs_nonneg M; omega
  have hsM : M ≤ s := by have := le_abs_self M; omega
  have hsq : s ≤ s ^ 2 := by nlinarith
  nlinarith



open ThreeCubes in
theorem solution{r : ℤ}
    (hr : r = 38 ∨ r = 52 ∨ r = 70 ∨ r = 146 ∨ r = 164 ∨ r = 178) (M : ℤ) :
    ∃ n : ℤ, M ≤ n ∧ n % 216 = r ∧ IsSumOfFourCubes n := by
  set s : ℤ := |M| + 1 with hs
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨648 * s ^ 2 + 38, le_quadratic_at_abs_succ (by norm_num) (by norm_num),
      by omega, isSumOfFourCubes_class38 s⟩
  · exact ⟨648 * s ^ 2 + 52, le_quadratic_at_abs_succ (by norm_num) (by norm_num),
      by omega, isSumOfFourCubes_class52 s⟩
  · exact ⟨432 * s ^ 2 + 70, le_quadratic_at_abs_succ (by norm_num) (by norm_num),
      by omega, isSumOfFourCubes_class70 s⟩
  · exact ⟨2592 * s ^ 2 + 794, le_quadratic_at_abs_succ (by norm_num) (by norm_num),
      by omega, isSumOfFourCubes_class146 s⟩
  · exact ⟨216 * s ^ 2 - 52, le_quadratic_at_abs_succ (by norm_num) (by norm_num),
      by omega, isSumOfFourCubes_class164 s⟩
  · exact ⟨432 * s ^ 2 - 38, le_quadratic_at_abs_succ (by norm_num) (by norm_num),
      by omega, isSumOfFourCubes_class178 s⟩
