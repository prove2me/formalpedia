-- Prove2me | solution 1 for ConvexOptimization.s_procedure
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-16T00:35:09.363061+00:00
-- url     : https://prove2.me/submissions/75c9d6c0-4cf0-4c24-af57-2257a1f19714

import Mathlib
import Definitions.Def_ConvexOptimization_quadraticForms
import Theorems.Thm_ConvexOptimization_single_constraint_quadratic_strong_duality

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

 theorem solution {nn : ℕ}
    (F₁ F₂ : Matrix (Fin nn) (Fin nn) ℝ) (hF₁ : F₁.IsSymm) (hF₂ : F₂.IsSymm)
    (g₁ g₂ : Fin nn → ℝ) (h₁ h₂ : ℝ)
    (xh : Fin nn → ℝ) (hxh : ConvexOptimization.quadForm F₁ g₁ h₁ xh < 0) :
    (∀ x, ConvexOptimization.quadForm F₁ g₁ h₁ x ≤ 0 →
      ConvexOptimization.quadForm F₂ g₂ h₂ x ≤ 0) ↔
      ∃ lam : ℝ, 0 ≤ lam ∧
        (lam • ConvexOptimization.symQuadBlock F₁ g₁ h₁ -
          ConvexOptimization.symQuadBlock F₂ g₂ h₂).PosSemidef := by
  have hq (x : Fin nn → ℝ) :
      ConvexOptimization.quadForm (-F₂) (-g₂) (-h₂) x =
        -ConvexOptimization.quadForm F₂ g₂ h₂ x := by
    simp [ConvexOptimization.quadForm, Matrix.neg_mulVec]
    ring
  have hb :
      ConvexOptimization.symQuadBlock (-F₂) (-g₂) (-h₂) =
        -ConvexOptimization.symQuadBlock F₂ g₂ h₂ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [ConvexOptimization.symQuadBlock]
  simpa [hq, hb, sub_eq_add_neg, add_comm] using
    (ConvexOptimization.single_constraint_quadratic_strong_duality
      (-F₂) F₁ hF₂.neg hF₁ (-g₂) g₁ (-h₂) h₁ xh hxh 0)
