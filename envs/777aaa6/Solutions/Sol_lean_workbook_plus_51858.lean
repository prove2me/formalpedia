-- Prove2me | solution 1 for lean_workbook_plus_51858
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:33.513481+00:00
-- url     : https://prove2.me/submissions/7b4d563e-300e-41fb-83ca-06132dbcef93

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ t : ℝ, 0 ≤ t ∧ t < 1 → 3 * t^2 * (4 + 20 * t + 31 * t^2 + 25 * t^3) ≥ 0 := by
  intro t
  intros
  have hpos_t : (0 : ℝ) ≤ t := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (3 * t^2 * (4 + 20 * t + 31 * t^2 + 25 * t^3)) - (0) := by
    calc
      0 ≤ ((39 / 4) : ℝ) * (1) * ((t + (2 * (t ^ 2))))^2 + ((9 / 4) : ℝ) * (1) * ((t + ((1 / 2) * (t ^ 2))))^2 + ((2055 / 128) : ℝ) * (t) * ((t + (2 * (t ^ 2))))^2 + ((345 / 128) : ℝ) * (t) * ((t + ((-2) * (t ^ 2))))^2 := by positivity
      _ = (3 * t^2 * (4 + 20 * t + 31 * t^2 + 25 * t^3)) - (0) := by ring
  exact sub_nonneg.mp h
