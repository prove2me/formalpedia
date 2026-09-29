-- Prove2me | Theorems.Thm_HappyEnd_cupCapNumber_recurrence
-- name    : HappyEnd.cupCapNumber_recurrence
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:22:49.774252+00:00
-- url     : https://prove2.me/theorems/2b9fdf17-508b-4b53-981c-c0902e5b72eb
-- title:
--   The Cup-Cap Recurrence: CC(j,k) = CC(j-1,k) + CC(j,k-1) - 1
-- statement:
--   **The Cup-Cap Recurrence**: CC(j,k) = CC(j-1,k) + CC(j,k-1) - 1
--   for j, k ≥ 3. This Pascal-type recurrence is the algebraic heart of the
--   Erdős–Szekeres inductive proof.
--
--   The proof reduces to Pascal's rule C(n+1, m+1) = C(n, m) + C(n, m+1)
--   with appropriate index shifts, then resolves the +1 bookkeeping with omega.
--
--   ```lean
--   theorem HappyEnd.cupCapNumber_recurrence(j k : ℕ) (hj : 3 ≤ j) (hk : 3 ≤ k) :
--       CupCapNumber j k = CupCapNumber (j - 1) k + CupCapNumber j (k - 1) - 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/ErdosSzekeres/CupCapBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/ErdosSzekeres/CupCapBound.lean#L58

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

theorem HappyEnd.cupCapNumber_recurrence(j k : ℕ) (hj : 3 ≤ j) (hk : 3 ≤ k) :
    CupCapNumber j k = CupCapNumber (j - 1) k + CupCapNumber j (k - 1) - 1 := by sorry
