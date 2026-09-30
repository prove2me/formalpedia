-- Prove2me | Theorems.Thm_Hirsch_finite_allocation_minkowski_criterion
-- name    : Hirsch.finite_allocation_minkowski_criterion
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T20:33:32.140338+00:00
-- url     : https://prove2.me/theorems/09c33216-ba2f-4c9f-b75e-e9d8279e8358
-- title:
--   Finite null tests imply whole-set Minkowski allocation
-- statement:
--   For finitely many continuous linear functionals a on a real normed space and a continuous linear generator map G from R^k, there is a fixed finite family of nonnegative null multipliers for the allocation rows (-aG,-I,ones). The family depends only on a and G. For every RHS b, every nonnegative scale t, and valid rowwise support bounds h on G({theta>=0:sum theta<=t}), the original H-polyhedron equals the sum of the erosion {a(p)<=b-h} and this finite-generator compact candidate exactly when every chosen multiplier gives a nonnegative test at every original point. The converse concludes one simultaneously feasible allocation, rather than assuming Farkas sufficiency. No boundedness, full dimensionality, simplicity, or generator independence is required. The support-indexed family has at most 2^(m+k+1) slots; no rank-plus-one enumeration, polynomial test count, executable catalogue correctness, elimination of the universal original-point quantifier, or Hirsch diameter bound is claimed.
-- source:
--   Classical compact separation and positive-circuit support reduction, composed in a bounded allocation system. Explicitly reuses the compact-feasibility core accepted in PR #216 (theorem a6e2a38d-00e3-46d6-b232-7cddee5e30e1) and the finite nonnegative-kernel tests accepted in PR #218 (theorem 8f3c4cc7-be73-4ecf-9e17-816c710e20d7), with those proofs inlined for a standalone packet. New work derives the complete bounded-simplex allocation alternative and the whole-set Minkowski equality. No classical novelty or arbitrary-polynomial-diameter claim.

import Mathlib
open Set
open scoped BigOperators

namespace Hirsch
theorem finite_allocation_minkowski_criterion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m k : ℕ) (a : Fin m → E →L[ℝ] ℝ)
    (G : (Fin k → ℝ) →L[ℝ] E) :
    ∃ c : Finset (Fin m ⊕ Option (Fin k)) → ((Fin m ⊕ Option (Fin k)) → ℝ),
      (∀ s, (∀ i, 0 ≤ c s i) ∧
        ∀ j, -(∑ i, c s (.inl i) * a i (G (Pi.single j (1 : ℝ)))) -
          c s (.inr (some j)) + c s (.inr none) = 0) ∧
      ∀ (b h : Fin m → ℝ) (t : ℝ), 0 ≤ t →
        (∀ θ : Fin k → ℝ, (∀ j, 0 ≤ θ j) → (∑ j, θ j) ≤ t →
          ∀ i, a i (G θ) ≤ h i) →
        (({x : E | ∀ i, a i x ≤ b i} =
          {x : E | ∃ p : E, (∀ i, a i p ≤ b i - h i) ∧
            ∃ θ : Fin k → ℝ, (∀ j, 0 ≤ θ j) ∧ (∑ j, θ j) ≤ t ∧ p + G θ = x}) ↔
        (∀ x : E, (∀ i, a i x ≤ b i) → ∀ s,
          0 ≤ (∑ i, c s (.inl i) * (b i - a i x - h i)) + c s (.inr none)*t)) := by sorry
end Hirsch
