-- Prove2me | solution 2 for EscapeCriterion.two_lt_norm_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T22:50:10.892968+00:00
-- url     : https://prove2.me/submissions/37e7a565-a379-439e-8da1-3c0e6a4437c4

import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_EscapeRateGreenFunction
open EscapeCriterion in
theorem solution {c z : ℂ} (hz : escapeRadius c < ‖z‖) (n : ℕ) : 2 < ‖orbit c z n‖ := by
  have h2 : 2 ≤ escapeRadius c := le_max_left _ _
  have hc : ‖c‖ ≤ escapeRadius c := le_max_right _ _
  have hstep : ∀ w : ℂ, escapeRadius c < ‖w‖ → escapeRadius c < ‖MandelbrotEscape.qmap c w‖ := by
    intro w hw
    have htri : ‖w‖ ^ 2 - ‖c‖ ≤ ‖MandelbrotEscape.qmap c w‖ := by
      unfold MandelbrotEscape.qmap
      have h := norm_sub_le (w ^ 2 + c) c
      simp only [add_sub_cancel_right, norm_pow] at h
      linarith
    nlinarith
  have hall : ∀ n, escapeRadius c < ‖orbit c z n‖ := by
    intro n
    induction n with
    | zero => simpa [orbit] using hz
    | succ n ih =>
      rw [orbit, Function.iterate_succ_apply']
      exact hstep _ ih
  linarith [hall n]
