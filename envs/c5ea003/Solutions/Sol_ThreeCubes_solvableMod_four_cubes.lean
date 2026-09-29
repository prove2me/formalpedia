-- Prove2me | solution 1 for ThreeCubes.solvableMod_four_cubes
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:03:06.066422+00:00
-- url     : https://prove2.me/submissions/4e500675-a545-44f8-9959-7a78cf4fa2de

-- Sol generated from Probability/FourCubes.lean
import Mathlib
import Definitions.Def_Probability_Basic
import Definitions.Def_Probability_FourCubes
import Theorems.Thm_ThreeCubes_solvableMod_of_mod_nine

/-!
# Four cubes: covering the residue classes

Over `ℤ` three cubes never represent `n ≡ ±4 (mod 9)`
(`ThreeCubes.not_isSumOfThreeCubes_of_mod_nine`) while five cubes always suffice
(`ThreeCubes.isSumOfFiveCubes`).  The four-cube problem sits exactly in between: there is *no*
congruence obstruction at all (four cubes cover every residue class modulo every modulus), and
it is a classical open problem whether every integer is a sum of four integer cubes.

This file proves the strongest covering result we could certify: an explicit finite system of
one-parameter polynomial identities

`(p₁k + q₁)³ + (p₂k + q₂)³ + (p₃k + q₃)³ + (p₄k + q₄)³ = 18k + r`

one for each admissible residue `r`, plus two identities with modulus `54`.  Each identity is a
polynomial identity checked by `ring`; they were found by a search over quadruples `(aᵢ)` with
`∑aᵢ³ = 0` and `(bᵢ)` with `∑aᵢ²bᵢ = 0`, which is exactly the condition for
`∑(aᵢt+bᵢ)³` to be a *linear* polynomial `3(∑aᵢbᵢ²)t + ∑bᵢ³`.

Main results.

* `ThreeCubes.isSumOfFourCubes_of_mod_eighteen` — every `n` whose residue mod `18` avoids
  `{2, 4, 5, 13, 14, 16}` is a sum of four integer cubes.  The four residues `4, 5, 13, 14`
  are exactly the classes `±4 (mod 9)`; these are *not* obstructed for four cubes
  (`4 = 1³+1³+1³+1³`), but no linear family was found meeting them.
* `ThreeCubes.isSumOfFourCubes_of_mod_fiftyfour` — the classes `±20 (mod 54)`, which lie inside
  the missing `±2 (mod 18)`, are covered as well.
* `ThreeCubes.isSumOfFourCubes_of_three_dvd` — in particular **every multiple of `3`** is a sum
  of four integer cubes, strengthening `ThreeCubes.isSumOfFourCubes_of_six_dvd`.
* `ThreeCubes.isSumOfFourCubes_of_not_exceptional` — the combined statement: every `n` with
  `n ≢ ±4 (mod 9)` and `n ≢ ±2, ±16 (mod 54)` is a sum of four integer cubes.  This covers
  `38` of the `54` residue classes modulo `54`; Demjanenko's theorem (not formalised here)
  asserts that all `42` classes with `n ≢ ±4 (mod 9)` are attainable.
* `ThreeCubes.isSumOfFourCubes_covers_all_residues` — the complementary local statement: modulo
  every positive modulus, four cubes represent every residue class, so no congruence
  obstruction exists for four cubes.
-/

open ThreeCubes



/-! ### The twelve linear families modulo `18` -/













/-! ### Two further families modulo `54` -/



/-! ### The covering theorems -/





/-! ### No congruence obstruction for four cubes -/



open ThreeCubes in
theorem solution{m : ℕ} (hm : 0 < m) (n : ℤ) :
    ∃ a b c d : ℤ, (m : ℤ) ∣ a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 - n := by
  obtain ⟨e, he3, h4, h5⟩ : ∃ e : ℤ, e ^ 3 = e ∧ (n - e) % 9 ≠ 4 ∧ (n - e) % 9 ≠ 5 := by
    rcases (by omega : n % 9 = 4 ∨ n % 9 = 5 ∨ (n % 9 ≠ 4 ∧ n % 9 ≠ 5)) with h | h | h
    · exact ⟨1, by norm_num, by omega, by omega⟩
    · exact ⟨-1, by norm_num, by omega, by omega⟩
    · exact ⟨0, by norm_num, by omega, by omega⟩
  obtain ⟨x, y, z, hxyz⟩ := solvableMod_of_mod_nine (n - e) h4 h5 m hm
  refine ⟨x, y, z, e, ?_⟩
  have hrw : x ^ 3 + y ^ 3 + z ^ 3 + e ^ 3 - n = x ^ 3 + y ^ 3 + z ^ 3 - (n - e) := by
    rw [he3]; ring
  rw [hrw]
  exact hxyz
