-- Prove2me | Theorems.Thm_ThreeCubes_not_isSumOfThreeCubes_of_mod_nine
-- name    : ThreeCubes.not_isSumOfThreeCubes_of_mod_nine
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:11:44.616361+00:00
-- url     : https://prove2.me/theorems/77c1a6bf-0c31-4085-924d-2be675bcc7a7
-- title:
--   The classical obstruction.
-- statement:
--   **The classical obstruction.** An integer congruent to `±4` mod `9` is not a sum of three
--   integer cubes.
--
--   ```lean
--   theorem ThreeCubes.not_isSumOfThreeCubes_of_mod_nine{n : ℤ} (h : n % 9 = 4 ∨ n % 9 = 5) :
--       ¬ IsSumOfThreeCubes n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/Basic.lean#L92

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

theorem ThreeCubes.not_isSumOfThreeCubes_of_mod_nine{n : ℤ} (h : n % 9 = 4 ∨ n % 9 = 5) :
    ¬ IsSumOfThreeCubes n := by sorry
