-- Prove2me | Theorems.Thm_ThreeCubes_mahler_one_injective
-- name    : ThreeCubes.mahler_one_injective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:10:54.255254+00:00
-- url     : https://prove2.me/theorems/b2b57690-91aa-4786-9fb3-3cb9d9b63700
-- title:
--   The number of representations of `1` as a sum of three cubes is unbounded: the map
-- statement:
--   The number of representations of `1` as a sum of three cubes is unbounded: the map
--   `t ↦ (9t⁴, 3t - 9t⁴, 1 - 9t³)` is injective on `ℤ`.
--
--   ```lean
--   theorem ThreeCubes.mahler_one_injective: Function.Injective
--       (fun t : ℤ => ((9 * t ^ 4 : ℤ), (3 * t - 9 * t ^ 4 : ℤ), (1 - 9 * t ^ 3 : ℤ))) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/Basic.lean#L118

-- Thm stub generated from Probability/Basic.lean
import Mathlib
import Definitions.Def_Probability_Basic

/-!
# Sums of three cubes: basic theory, the mod 9 obstruction, and parametric families

This file sets up the arithmetic of the affine cubic surface
`x³ + y³ + z³ = n` over `ℤ`.

Main contents.

* `ThreeCubes.IsSumOfThreeCubes` — the predicate `∃ x y z : ℤ, x³ + y³ + z³ = n`.
* `ThreeCubes.SolvableMod` / `ThreeCubes.LocallySolvable` — solvability of the
  congruence `x³ + y³ + z³ ≡ n (mod m)`, for one modulus and for all moduli.
* `ThreeCubes.not_isSumOfThreeCubes_of_mod_nine` — the classical congruence
  obstruction: `n ≡ ±4 (mod 9)` is never a sum of three cubes.
* Closure properties: negation, cubic scaling, translation by a cube.
* Two classical one-parameter families showing that `1` and `2` have infinitely
  many representations, and hence that the representation-counting function is
  unbounded.

The deeper statement that `n ≢ ±4 (mod 9)` is the *only* obstruction to local
solvability is proved in `Probability.ThreeCubes.LocalSolvability`.
-/

open ThreeCubes




/-! ### Elementary closure properties -/






/-! ### The mod 9 obstruction -/








/-! ### Parametric families -/

theorem ThreeCubes.mahler_one_injective: Function.Injective
    (fun t : ℤ => ((9 * t ^ 4 : ℤ), (3 * t - 9 * t ^ 4 : ℤ), (1 - 9 * t ^ 3 : ℤ))) := by sorry
