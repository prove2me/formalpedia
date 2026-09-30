-- Prove2me | Theorems.Thm_RybinAI2026_P01_psi_fractional_kernel_representation
-- name    : RybinAI2026.P01.psi_fractional_kernel_representation
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T02:30:11.260293+00:00
-- url     : https://prove2.me/theorems/64dc0eff-49af-4801-966e-63b6ef0ec872
-- title:
--   Finite-interval fractional transform of psi
-- statement:
--   For u>0, the scalar integral psi(u^2)=integral_0^1 (1+(u^2-1)s^2)^(-1) ds equals the finite-interval integral with kernel (2r(1-r)+u(r^2+(1-r)^2))^(-1). It follows from the increasing fractional substitution s=r/(u+(1-u)r).
-- source:
--   This is the exact finite-interval change of variables needed to prove the scaled-psi monotonicities in the aligned diagonal pair-contraction argument from artifacts/p01_slack/2026-09-29-no-w-pair.md. For u>0, s(r)=r/(u+(1-u)r) maps [0,1] increasingly onto [0,1], and direct algebra transforms the integrand times s'(r) to the stated kernel. It is independent of the Open matrix-integral root and does not assume the root or any unproved auxiliary theorem.

import Mathlib

theorem RybinAI2026.P01.psi_fractional_kernel_representation (u : ℝ) (hu : 0 < u) :
    ∫ s in (0 : ℝ)..1, (1 + (u ^ 2 - 1) * s ^ 2)⁻¹ =
      ∫ r in (0 : ℝ)..1,
        (2 * r * (1 - r) + u * (r ^ 2 + (1 - r) ^ 2))⁻¹ := by
  sorry
