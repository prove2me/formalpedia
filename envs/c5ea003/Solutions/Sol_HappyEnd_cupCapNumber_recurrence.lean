-- Prove2me | solution 1 for HappyEnd.cupCapNumber_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:16:01.557817+00:00
-- url     : https://prove2.me/submissions/d477400e-44d4-4625-be60-8addddd92381

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
theorem solution(j k : ℕ) (hj : 3 ≤ j) (hk : 3 ≤ k) :
    CupCapNumber j k = CupCapNumber (j - 1) k + CupCapNumber j (k - 1) - 1 := by
  simp only [CupCapNumber]
  simp only [show ¬(j < 2) by omega, show ¬(k < 2) by omega,
             show ¬(j - 1 < 2) by omega, show ¬(k - 1 < 2) by omega,
             false_or, ite_false]
  rw [show j - 1 + k - 4 = j + k - 5 from by omega,
      show j - 1 - 2 = j - 3 from by omega,
      show j + (k - 1) - 4 = j + k - 5 from by omega]
  have pascal : Nat.choose (j + k - 4) (j - 2) =
      Nat.choose (j + k - 5) (j - 3) + Nat.choose (j + k - 5) (j - 2) := by
    rw [show j + k - 4 = (j + k - 5) + 1 from by omega,
        show j - 2 = (j - 3) + 1 from by omega]
    exact (Nat.choose_succ_succ (j + k - 5) (j - 3)).symm
  omega
