-- Prove2me | Theorems.Thm_ThreeCubes_not_solvableMod_nine
-- name    : ThreeCubes.not_solvableMod_nine
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:12:17.838777+00:00
-- url     : https://prove2.me/theorems/c38682b9-d63e-4afe-a81e-a652a6da2a71
-- title:
--   Congruence obstruction.
-- statement:
--   **Congruence obstruction.**  If `n ≡ 4` or `n ≡ 5 (mod 9)` then `x³ + y³ + z³ ≡ n (mod 9)`
--   has no solution.
--
--   ```lean
--   theorem ThreeCubes.not_solvableMod_nine{n : ℤ} (h : n % 9 = 4 ∨ n % 9 = 5) : ¬ SolvableMod 9 n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/Basic.lean#L75

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

theorem ThreeCubes.not_solvableMod_nine{n : ℤ} (h : n % 9 = 4 ∨ n % 9 = 5) : ¬ SolvableMod 9 n := by sorry
