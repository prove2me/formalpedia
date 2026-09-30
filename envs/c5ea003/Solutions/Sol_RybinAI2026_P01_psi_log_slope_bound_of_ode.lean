-- Prove2me | solution 1 for RybinAI2026.P01.psi_log_slope_bound_of_ode
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T00:22:00.78159+00:00
-- url     : https://prove2.me/submissions/79e5a28f-cc32-4a4f-a0dd-10881e52e5fa

import Mathlib
import Theorems.Thm_RybinAI2026_P01_eta_envelope_of_sqrt_comparison

theorem solution (t ψ ψ' : ℝ) (ht : 0 < t) (hψ : 0 < ψ)
    (hODE : 2 * (t - 1) * ψ' = 1 / t - ψ)
    (hAtOne : t = 1 → ψ' ≤ -(1 / 4 : ℝ))
    (hhi : 1 < t → 1 / Real.sqrt t ≤ ψ)
    (hlo : t < 1 → ψ ≤ 1 / Real.sqrt t) :
    1 / 2 + t * ψ' / ψ ≤ 1 / (2 * (1 + Real.sqrt t)) := by
  by_cases heq : t = 1
  · have hψone : ψ = 1 := by
      rw [heq] at hODE
      norm_num at hODE
      linarith
    have hlim := hAtOne heq
    have hnum : (1 : ℝ) / 2 + ψ' ≤ 1 / 4 := by linarith
    rw [heq, hψone]
    norm_num at hnum
    norm_num
    linarith
  · have heta := RybinAI2026.P01.eta_envelope_of_sqrt_comparison t ψ ht hψ hhi hlo
    rw [if_neg heq] at heta
    have htne : t - 1 ≠ 0 := sub_ne_zero.mpr heq
    have hmul := congrArg (fun z : ℝ => t * z) hODE
    have hODE' : 2 * t * (t - 1) * ψ' = 1 - t * ψ := by
      field_simp [ht.ne'] at hmul
      nlinarith [hmul]
    have hrewrite : (1 - ψ) / (2 * (t - 1) * ψ) =
        1 / 2 + t * ψ' / ψ := by
      field_simp [ht.ne', hψ.ne', htne]
      nlinarith [hODE']
    rw [← hrewrite]
    exact heta
