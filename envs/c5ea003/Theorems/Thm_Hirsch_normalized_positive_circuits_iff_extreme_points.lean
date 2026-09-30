-- Prove2me | Theorems.Thm_Hirsch_normalized_positive_circuits_iff_extreme_points
-- name    : Hirsch.normalized_positive_circuits_iff_extreme_points
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T21:31:21.2744+00:00
-- url     : https://prove2.me/theorems/56d0cf40-7b2f-49cb-98c5-fe6a074637d5
-- title:
--   Normalized positive circuits are exactly the vertices of the nonnegative kernel section
-- statement:
--   For every real linear map A from R^n to R^k, the extreme points of the normalized nonnegative kernel {x>=0: A x=0, sum x=1} are exactly its support-minimal nonzero nonnegative null vectors, with total mass one. Support minimality is quantified over all nonzero nonnegative null vectors, not just normalized vectors. No full-rank, nonempty-section, bounded original-polyhedron, circuit-generation, RREF, vertex-enumeration or catalogue-completeness premise is assumed. This identifies the canonical vectors that exact normalized-kernel vertex enumeration must return; it does not prove a particular imperative enumeration program correct or supply a graph-diameter bound.
-- source:
--   Classical positive-circuit/extreme-ray characterization. Direct proof reuses accepted #218 support pruning and ray uniqueness; geometric extremality is Mathlib Set.extremePoints. Historical conformal decomposition #25 is already accepted and is not resubmitted. Related classical exposition: Mueller--Regensburger, arXiv:1512.00267. No novelty claim.

import Mathlib
open scoped BigOperators

namespace Hirsch
theorem normalized_positive_circuits_iff_extreme_points (n k : ℕ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (x : Fin n → ℝ) :
    (x ∈ Set.extremePoints ℝ
      {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ A z = 0 ∧ (∑ i, z i) = 1}) ↔
      ((∀ i, 0 ≤ x i) ∧ A x = 0 ∧ (∑ i, x i) = 1 ∧
        (∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) → A y = 0 → y ≠ 0 →
          Function.support y ⊆ Function.support x →
          Function.support x ⊆ Function.support y)) := by sorry
end Hirsch
