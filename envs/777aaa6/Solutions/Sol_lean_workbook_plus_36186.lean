-- Prove2me | solution 1 for lean_workbook_plus_36186
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:38.816605+00:00
-- url     : https://prove2.me/submissions/3f353db1-f2cc-403e-bba8-0a84099ef616

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 2 * (a^2 + b^2 + 2) ≥ 2 * (a + 1) * (b + 1) := by
  intros
  have h : (0 : ℝ) ≤ (2 * (a^2 + b^2 + 2)) - (2 * (a + 1) * (b + 1)) := by
    calc
      0 ≤ (1 : ℝ) * ((1 + ((-1) * b)))^2 + (1 : ℝ) * ((1 + ((-1) * a)))^2 + (1 : ℝ) * ((b + ((-1) * a)))^2 := by positivity
      _ = (2 * (a^2 + b^2 + 2)) - (2 * (a + 1) * (b + 1)) := by ring
  exact sub_nonneg.mp h
