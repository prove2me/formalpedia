-- Prove2me | solution 1 for HappyEnd.cupCapNumber_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:16:02.205708+00:00
-- url     : https://prove2.me/submissions/b12af67a-1e5a-41f8-a86e-585c7afa828c

-- Sol generated from Geometry/ErdosSzekeres/CupCapBound.lean
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


/-! ## Convex Layer Decomposition (Novel Definition) -/





/-! ## The Cup-Cap Theorem Statement -/


/-! ## Growth Bounds -/


/-
CC(j,k) ≥ j when k ≥ j and j ≥ 2. Note: CC(j,2) = 2 for all j,
so the bound j ≤ CC(j,k) requires k ≥ j (or at least k ≥ 3 for j ≥ 3).
-/

/-! ## Conjecture: Cup-Cap Tightness -/



open HappyEnd in
theorem solution(j k : ℕ) :
    CupCapNumber j k = CupCapNumber k j := by
  simp only [CupCapNumber]
  split
  · rename_i h; split
    · rfl
    · rename_i h2; push_neg at h2; rcases h with hj | hk <;> simp_all <;> omega
  · rename_i h; push_neg at h; split
    · rename_i h2; rcases h2 with hk | hj <;> simp_all <;> omega
    · rename_i h2; push_neg at h2
      congr 1
      rw [show k + j - 4 = j + k - 4 from by omega,
          show k - 2 = j + k - 4 - (j - 2) from by omega]
      exact (Nat.choose_symm (by omega)).symm
