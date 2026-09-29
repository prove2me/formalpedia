-- Prove2me | solution 1 for ConvexOptimization.dualFunction_concave
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-15T03:41:14.834373+00:00
-- url     : https://prove2.me/submissions/2ad08203-fbd2-4c9a-913f-da70b704f3ae

import Mathlib
import Definitions.Def_ConvexOptimization_lagrangeDuality

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem solution {n mm p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ)
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (lam₁ lam₂ : Fin mm → ℝ) (nu₁ nu₂ : Fin p → ℝ)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (θ : EReal) * ConvexOptimization.dualFunction f₀ fc a b lam₁ nu₁ +
      ((1 - θ : ℝ) : EReal) * ConvexOptimization.dualFunction f₀ fc a b lam₂ nu₂ ≤
    ConvexOptimization.dualFunction f₀ fc a b
      (fun i => θ * lam₁ i + (1 - θ) * lam₂ i)
      (fun j => θ * nu₁ j + (1 - θ) * nu₂ j) := by
  apply le_iInf
  intro x
  have h₁ : ConvexOptimization.dualFunction f₀ fc a b lam₁ nu₁ ≤
      (ConvexOptimization.lagrangian f₀ fc a b x lam₁ nu₁ : EReal) :=
    iInf_le _ x
  have h₂ : ConvexOptimization.dualFunction f₀ fc a b lam₂ nu₂ ≤
      (ConvexOptimization.lagrangian f₀ fc a b x lam₂ nu₂ : EReal) :=
    iInf_le _ x
  calc
    (θ : EReal) * ConvexOptimization.dualFunction f₀ fc a b lam₁ nu₁ +
        ((1 - θ : ℝ) : EReal) * ConvexOptimization.dualFunction f₀ fc a b lam₂ nu₂ ≤
      (θ : EReal) * (ConvexOptimization.lagrangian f₀ fc a b x lam₁ nu₁ : EReal) +
        ((1 - θ : ℝ) : EReal) *
          (ConvexOptimization.lagrangian f₀ fc a b x lam₂ nu₂ : EReal) := by
            gcongr
    _ = (ConvexOptimization.lagrangian f₀ fc a b x
        (fun i => θ * lam₁ i + (1 - θ) * lam₂ i)
        (fun j => θ * nu₁ j + (1 - θ) * nu₂ j) : EReal) := by
      have hi :
          (∑ i, (θ * lam₁ i + (1 - θ) * lam₂ i) * fc i x) =
            θ * ∑ i, lam₁ i * fc i x + (1 - θ) * ∑ i, lam₂ i * fc i x := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      have hj :
          (∑ j, (θ * nu₁ j + (1 - θ) * nu₂ j) * (⟪a j, x⟫ - b j)) =
            θ * ∑ j, nu₁ j * (⟪a j, x⟫ - b j) +
              (1 - θ) * ∑ j, nu₂ j * (⟪a j, x⟫ - b j) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      norm_cast
      simp only [ConvexOptimization.lagrangian]
      rw [hi, hj]
      ring
