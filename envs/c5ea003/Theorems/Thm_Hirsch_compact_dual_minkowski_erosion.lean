-- Prove2me | Theorems.Thm_Hirsch_compact_dual_minkowski_erosion
-- name    : Hirsch.compact_dual_minkowski_erosion
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T19:09:39.369056+00:00
-- url     : https://prove2.me/theorems/a6e2a38d-00e3-46d6-b232-7cddee5e30e1
-- title:
--   Compact dual sufficiency for whole-polyhedron Minkowski erosion
-- statement:
--   Let E be a real normed vector space, let a_i be a finite family of continuous real linear functionals, let Q be compact and convex, and suppose a_i(q) <= h_i for all q in Q. Set R={x: a_i(x)<=b_i for every i} and P={p: a_i(p)<=b_i-h_i for every i}. Then R=P+Q if and only if, for every x in R and every nonnegative weight vector w, there is q in Q with sum_i w_i(a_i(x)+h_i-b_i) <= sum_i w_i a_i(q). This is the full geometric sufficiency direction, not an assumption of simultaneous feasibility. All nonnegative weights are quantified: reducing to a finite positive-circuit list remains a separate theorem. It imposes no boundedness or full-dimensionality assumption on R. This classical separation consequence is a reusable candidate-extraction lemma, not a proof of Polynomial Hirsch.
-- source:
--   Standalone original-inequality interface derived from Mathlib ProperCone.hyperplane_separation at https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Analysis/Convex/Cone/Dual.lean ; geometric Hahn-Banach/Farkas separation. No claim of classical novelty.

import Mathlib
open Set
open scoped BigOperators

namespace Hirsch
theorem compact_dual_minkowski_erosion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (a : Fin m → E →L[ℝ] ℝ) (b h : Fin m → ℝ)
    (Q : Set E) (hQ : IsCompact Q) (hconv : Convex ℝ Q)
    (hsupport : ∀ q ∈ Q, ∀ i, a i q ≤ h i) :
    ({x : E | ∀ i, a i x ≤ b i} =
      {x : E | ∃ p : E, (∀ i, a i p ≤ b i - h i) ∧
        ∃ q ∈ Q, p + q = x}) ↔
    (∀ x : E, (∀ i, a i x ≤ b i) →
      ∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
        ∃ q ∈ Q, (∑ i, w i * (a i x + h i - b i)) ≤
          ∑ i, w i * a i q) := by sorry
end Hirsch
