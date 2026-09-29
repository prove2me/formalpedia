-- Prove2me | Theorems.Thm_HappyEnd_three_point_cup_or_cap
-- name    : HappyEnd.three_point_cup_or_cap
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:23:06.825117+00:00
-- url     : https://prove2.me/theorems/14d2a320-60d1-4081-b582-7e891b53ba0e
-- title:
--   Three-point dichotomy: Among 3 points in general position,
-- statement:
--   **Three-point dichotomy**: Among 3 points in general position,
--   they form either a cup (orient > 0) or a cap (orient < 0).
--   This is the base case of the cup-cap induction, corresponding to CC(3,3) = 3.
--
--   Proof by `by_contra` and case analysis: since general position excludes
--   orient = 0, the orientation must be strictly positive or negative. Each
--   case provides the required witness.
--
--   ```lean
--   theorem HappyEnd.three_point_cup_or_cap{p : Fin 3 → ℝ × ℝ}
--       (hgp : GeneralPosition p) :
--       HasCup p 3 ∨ HasCap p 3 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/ErdosSzekeres/CupCapBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/ErdosSzekeres/CupCapBound.lean#L253

-- Thm stub generated from Geometry/ErdosSzekeres/CupCapBound.lean
import Mathlib
import Definitions.Def_Geometry_ErdosSzekeres_CupCapBound
/-
# Cup-Cap Inductive Theory and ES Upper Bound

This file develops the combinatorial core of the Erdős–Szekeres cup-cap theorem:
the function CC(j,k) = C(j+k-4, j-2) + 1 satisfying the Pascal recurrence
CC(j,k) = CC(j-1,k) + CC(j,k-1) - 1, with base cases CC(2,k) = CC(j,2) = 2.

We introduce a novel **convex layer decomposition** (onion peeling) structure
that provides a quantitative measure of geometric complexity beyond the binary
notion of convex position.

## Main results

- `CupCapNumber`: CC(j,k) = C(j+k-4, j-2) + 1
- `cupCapNumber_base_left` / `cupCapNumber_base_right`: CC(2,k) = CC(j,2) = 2
- `cupCapNumber_recurrence`: CC(j,k) = CC(j-1,k) + CC(j,k-1) - 1 for j,k ≥ 3
- `cupCapNumber_symmetric`: CC(j,k) = CC(k,j) via Vandermonde symmetry
- `ConvexLayerDecomposition`: Novel structure for onion peeling
- `layers_le_points`: Each decomposition has ≤ m layers (by surjection argument)
- `cup_mono` / `cap_mono`: Size monotonicity for cups and caps
- `cup_iff_cap_reflect`: Duality via y-reflection
- `three_point_cup_or_cap`: Any 3 general-position points form a cup or cap
- `orient_cup_extend` / `orient_cap_extend`: Orientation transitivity
-/

open Finset Nat Function BigOperators

open HappyEnd

/-! ## The Cup-Cap Number -/


/-! ## Base Cases -/



/-! ## The Recurrence via Pascal's Rule -/


/-! ## Symmetry -/


/-! ## Specific Values -/




/-! ## The ES Upper Bound Formula -/


/-! ## Geometric Definitions -/






/-! ## Cup and Cap Monotonicity -/



/-! ## Orientation Algebraic Properties -/






/-! ## Orientation Transitivity -/



/-! ## Cup-Cap Duality via Reflection -/



/-! ## Structural Lemma: Three-Point Dichotomy -/

theorem HappyEnd.three_point_cup_or_cap{p : Fin 3 → ℝ × ℝ}
    (hgp : GeneralPosition p) :
    HasCup p 3 ∨ HasCap p 3 := by sorry
