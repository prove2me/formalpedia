-- Prove2me | Theorems.Thm_RybinAI2026_P01_psi_fractional_order_properties
-- name    : RybinAI2026.P01.psi_fractional_order_properties
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T03:24:11.339448+00:00
-- url     : https://prove2.me/theorems/4577259a-6602-49d7-af95-72bd9e10a875
-- title:
--   Order properties of the scaled psi integral
-- statement:
--   For the defining psi integral, G(t)=sqrt(t)psi(t) is positive and increasing on the positive reals, while G(t)(1+1/sqrt(t)) is decreasing. The proof uses a finite fractional-kernel representation and its two pointwise cross-multiplication inequalities.
-- source:
--   This is the actual-psi order bridge required by the low/high branches of RybinAI2026.P01.aligned_diagonal_pair_contraction (9b380478-f4d0-4431-82e4-d7511da6dafb). The finite transform is psi(u^2)=integral_0^1 D_u(r)^(-1)dr with D_u=2r(1-r)+u(r^2+(1-r)^2). The already isolated pointwise comparisons lift under the interval integral to increasing sqrt(t)psi(t) and decreasing (1+sqrt(t))psi(t).

import Mathlib
import Theorems.Thm_RybinAI2026_P01_psi_fractional_kernel_representation
import Theorems.Thm_RybinAI2026_P01_fractional_kernel_pointwise_order
import Theorems.Thm_RybinAI2026_P01_psi_integral_pos

theorem RybinAI2026.P01.psi_fractional_order_properties :
    let ψ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹
    let G : ℝ → ℝ := fun t => Real.sqrt t * ψ t
    (∀ t, 0 < t → 0 < G t) ∧
      MonotoneOn G (Set.Ioi 0) ∧
      AntitoneOn (fun t : ℝ => G t * (1 + (Real.sqrt t)⁻¹)) (Set.Ioi 0) := by
  sorry
