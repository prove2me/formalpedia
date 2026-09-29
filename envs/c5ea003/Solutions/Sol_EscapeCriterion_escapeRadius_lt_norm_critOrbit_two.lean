-- Prove2me | solution 1 for EscapeCriterion.escapeRadius_lt_norm_critOrbit_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T01:06:39.290988+00:00
-- url     : https://prove2.me/submissions/80c0d659-c766-4b16-b370-bbc7ed527471

import Mathlib
import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_EscapeDoublyExponential
import Definitions.Def_Novelty_EscapeRateGreenFunction
open EscapeCriterion MandelbrotEscape in
theorem solution {c : ℂ} (hc : 2 < ‖c‖) : escapeRadius c < ‖orbit c 0 2‖ := by
  -- two steps from the critical point: `0 ↦ c ↦ c² + c`
  have horb : orbit c 0 2 = c ^ 2 + c := by
    simp [orbit, qmap]
  have hR : escapeRadius c = ‖c‖ := by
    unfold escapeRadius
    exact max_eq_right hc.le
  rw [horb, hR]
  -- reverse triangle inequality: `‖c² + c‖ ≥ ‖c‖² - ‖c‖ = ‖c‖ (‖c‖ - 1) > ‖c‖`
  have h1 : ‖c‖ ^ 2 - ‖c‖ ≤ ‖c ^ 2 + c‖ := by
    have := norm_sub_le (c ^ 2 + c) c
    rw [add_sub_cancel_right, norm_pow] at this
    linarith
  nlinarith
