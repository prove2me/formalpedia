-- Prove2me | solution 1 for ConvexOptimization.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-15T03:41:58.152327+00:00
-- url     : https://prove2.me/submissions/19de76e0-bf25-4056-9fa9-372629a0251e

import Mathlib
import Definitions.Def_ConvexOptimization_lagrangeDuality

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem solution {n mm p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ)
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (lam : Fin mm → ℝ) (hlam : ∀ i, 0 ≤ lam i) (nu : Fin p → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ ConvexOptimization.feasibleSet fc a b) :
    ConvexOptimization.dualFunction f₀ fc a b lam nu ≤ (f₀ x : EReal) := by
  refine (iInf_le
    (fun y : EuclideanSpace ℝ (Fin n) =>
      (ConvexOptimization.lagrangian f₀ fc a b y lam nu : EReal)) x).trans ?_
  change ((ConvexOptimization.lagrangian f₀ fc a b x lam nu : ℝ) : EReal) ≤
    (f₀ x : EReal)
  norm_cast
  change (∀ i, fc i x ≤ 0) ∧ (∀ j, ⟪a j, x⟫ = b j) at hx
  have hi : ∑ i, lam i * fc i x ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    exact mul_nonpos_of_nonneg_of_nonpos (hlam i) (hx.1 i)
  have hj : ∑ j, nu j * (⟪a j, x⟫ - b j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hx.2 j]
    ring
  simp only [ConvexOptimization.lagrangian]
  linarith
