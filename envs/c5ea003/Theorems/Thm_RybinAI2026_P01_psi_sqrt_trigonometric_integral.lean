-- Prove2me | Theorems.Thm_RybinAI2026_P01_psi_sqrt_trigonometric_integral
-- name    : RybinAI2026.P01.psi_sqrt_trigonometric_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T01:11:28.621759+00:00
-- url     : https://prove2.me/theorems/fcadec43-10aa-4bf1-bfb1-6cabb6151e48
-- title:
--   Finite trigonometric representation of the scaled psi integral
-- statement:
--   For every positive t, the scaled scalar integral sqrt(t) times integral_0^1 (1+(t-1)s^2)^(-1) ds equals a finite trigonometric integral over [0,pi/2] with kernel (1+(2/sqrt(t)) sin(theta) cos(theta))^(-1). The identity follows from the increasing substitution s=sin(theta)/(sqrt(t) cos(theta)+sin(theta)).
-- source:
--   Derived as an exact change of variables from the defining psi integral used in the aligned diagonal pair-contraction proof, artifacts/p01_slack/2026-09-29-no-w-pair.md. Its purpose is to prove monotonicity of G(t)=sqrt(t)*psi(t) and antitonicity of G(t)*(1+1/sqrt(t)) by pointwise comparison, bypassing differentiation under the integral.

import Mathlib

theorem RybinAI2026.P01.psi_sqrt_trigonometric_integral (t : ℝ) (ht : 0 < t) :
    Real.sqrt t * (∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹) =
      ∫ θ in (0 : ℝ)..(Real.pi / 2),
        (1 + (2 / Real.sqrt t) * Real.sin θ * Real.cos θ)⁻¹ := by
  sorry
