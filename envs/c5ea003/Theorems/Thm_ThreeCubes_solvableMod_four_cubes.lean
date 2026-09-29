-- Prove2me | Theorems.Thm_ThreeCubes_solvableMod_four_cubes
-- name    : ThreeCubes.solvableMod_four_cubes
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:14:40.277475+00:00
-- url     : https://prove2.me/theorems/d3185a99-aee3-433f-883a-9d53eb7f59a7
-- title:
--   Four cubes have no congruence obstruction.
-- statement:
--   **Four cubes have no congruence obstruction.**  For every modulus `m > 0` and every `n`
--   the congruence `a³ + b³ + c³ + d³ ≡ n (mod m)` is solvable: one of `n`, `n - 1`, `n + 1`
--   avoids the classes `±4 (mod 9)`, and the shift is itself a cube.  Contrast
--   `ThreeCubes.forall_solvableMod_iff`, where the modulus `9` genuinely obstructs three cubes.
--
--   ```lean
--   theorem ThreeCubes.solvableMod_four_cubes{m : ℕ} (hm : 0 < m) (n : ℤ) :
--       ∃ a b c d : ℤ, (m : ℤ) ∣ a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 - n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/FourCubes.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/FourCubes.lean#L155

-- Thm stub generated from Probability/FourCubes.lean
import Mathlib
import Definitions.Def_Probability_FourCubes

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

theorem ThreeCubes.solvableMod_four_cubes{m : ℕ} (hm : 0 < m) (n : ℤ) :
    ∃ a b c d : ℤ, (m : ℤ) ∣ a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 - n := by sorry
