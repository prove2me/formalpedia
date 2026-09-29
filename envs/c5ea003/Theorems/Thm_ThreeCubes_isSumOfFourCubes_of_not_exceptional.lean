-- Prove2me | Theorems.Thm_ThreeCubes_isSumOfFourCubes_of_not_exceptional
-- name    : ThreeCubes.isSumOfFourCubes_of_not_exceptional
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:14:00.329372+00:00
-- url     : https://prove2.me/theorems/ae03136a-acf1-49e0-8c53-deb063956d94
-- title:
--   The combined covering theorem.
-- statement:
--   **The combined covering theorem.**  Every integer `n` with `n ≢ ±4 (mod 9)` and
--   `n ≢ ±2, ±16 (mod 54)` is a sum of four integer cubes; that is `38` of the `54` residue classes
--   modulo `54`.  (Recall `38 ≡ -16` and `52 ≡ -2` modulo `54`.)
--
--   ```lean
--   theorem ThreeCubes.isSumOfFourCubes_of_not_exceptional{n : ℤ} (h4 : n % 9 ≠ 4) (h5 : n % 9 ≠ 5)
--       (e2 : n % 54 ≠ 2) (e16 : n % 54 ≠ 16) (e38 : n % 54 ≠ 38) (e52 : n % 54 ≠ 52) :
--       IsSumOfFourCubes n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/FourCubes.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/FourCubes.lean#L142

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

theorem ThreeCubes.isSumOfFourCubes_of_not_exceptional{n : ℤ} (h4 : n % 9 ≠ 4) (h5 : n % 9 ≠ 5)
    (e2 : n % 54 ≠ 2) (e16 : n % 54 ≠ 16) (e38 : n % 54 ≠ 38) (e52 : n % 54 ≠ 52) :
    IsSumOfFourCubes n := by sorry
