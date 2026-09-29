-- Prove2me | solution 1 for lean_workbook_plus_30881
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:58:28.295812+00:00
-- url     : https://prove2.me/submissions/73228266-4982-4d67-adb6-07dd63ac5705

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1) : 4 * (a * b * c + 1) ≥ (a + 1) * (b + 1) * (c + 1) := by
  have ha0 : 0 ≤ a-1 := by linarith
  have hb0 : 0 ≤ b-1 := by linarith
  have hc0 : 0 ≤ c-1 := by linarith
  have hp := mul_nonneg ha0 hb0
  have hq := mul_nonneg hb0 hc0
  have hr := mul_nonneg hc0 ha0
  have hs := mul_nonneg hp hc0
  nlinarith
