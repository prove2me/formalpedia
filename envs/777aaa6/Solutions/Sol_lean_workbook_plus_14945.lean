-- Prove2me | solution 1 for lean_workbook_plus_14945
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:41:01.893537+00:00
-- url     : https://prove2.me/submissions/fc30c3ed-b50d-45c9-9117-8e5da0b8b721

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ t : ℝ, t^2 * (3 * t^2 - 8 * t + 6) ≥ 0 := by
  intro t
  intros
  have h : (0 : ℝ) ≤ (t^2 * (3 * t^2 - 8 * t + 6)) - (0) := by
    calc
      0 ≤ (2 : ℝ) * ((t + ((-1) * (t ^ 2))))^2 + (4 : ℝ) * ((t + ((-1 / 2) * (t ^ 2))))^2 := by positivity
      _ = (t^2 * (3 * t^2 - 8 * t + 6)) - (0) := by ring
  exact sub_nonneg.mp h
