-- Prove2me | solution 1 for lean_workbook_plus_48427
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:29:05.221563+00:00
-- url     : https://prove2.me/submissions/fed665e2-ff3d-4d21-9fd0-3ce3fd88ed49

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ c : ℝ, (c - 1) ^ 2 * (71 * c ^ 2 + 2 * c + 631) ≥ 0 := by
  intro c
  intros
  have h : (0 : ℝ) ≤ ((c - 1) ^ 2 * (71 * c ^ 2 + 2 * c + 631)) - (0) := by
    calc
      0 ≤ (630 : ℝ) * ((1 + ((-1) * c)))^2 + (1 : ℝ) * ((1 + ((-1) * (c ^ 2))))^2 + (70 : ℝ) * ((c + ((-1) * (c ^ 2))))^2 := by positivity
      _ = ((c - 1) ^ 2 * (71 * c ^ 2 + 2 * c + 631)) - (0) := by ring
  exact sub_nonneg.mp h
