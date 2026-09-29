-- Prove2me | Theorems.Thm_ThreeCubes_isSumOfFourCubes_of_mod_eighteen
-- name    : ThreeCubes.isSumOfFourCubes_of_mod_eighteen
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:13:49.106004+00:00
-- url     : https://prove2.me/theorems/22820cc8-1146-403b-93c7-c24189107d51
-- title:
--   Twelve of the fourteen admissible residues modulo `18`.
-- statement:
--   **Twelve of the fourteen admissible residues modulo `18`.**  Every integer whose residue
--   modulo `18` is not one of `2, 4, 5, 13, 14, 16` is a sum of four integer cubes.  The classes
--   `4, 5, 13, 14` are precisely `±4 (mod 9)`; these are excluded only because no linear
--   one-parameter family was found for them, not because of a congruence obstruction
--   (`ThreeCubes.solvableMod_four_cubes`).
--
--   ```lean
--   theorem ThreeCubes.isSumOfFourCubes_of_mod_eighteen{n : ℤ}
--       (h2 : n % 18 ≠ 2) (h4 : n % 18 ≠ 4) (h5 : n % 18 ≠ 5) (h13 : n % 18 ≠ 13)
--       (h14 : n % 18 ≠ 14) (h16 : n % 18 ≠ 16) : IsSumOfFourCubes n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/FourCubes.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/FourCubes.lean#L100

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

theorem ThreeCubes.isSumOfFourCubes_of_mod_eighteen{n : ℤ}
    (h2 : n % 18 ≠ 2) (h4 : n % 18 ≠ 4) (h5 : n % 18 ≠ 5) (h13 : n % 18 ≠ 13)
    (h14 : n % 18 ≠ 14) (h16 : n % 18 ≠ 16) : IsSumOfFourCubes n := by sorry
