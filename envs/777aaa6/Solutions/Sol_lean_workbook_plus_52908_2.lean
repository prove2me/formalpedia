-- Prove2me | solution 2 for lean_workbook_plus_52908
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:17:52.521064+00:00
-- url     : https://prove2.me/submissions/bff0c9f4-10bb-4ae1-9e30-5f64b33ed163

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℝ) : 3 * a * (a + 4) ≤ (3 * a + a + 4) ^ 2 / 4 := by
  intros
  have h : (0 : ℝ) ≤ ((3 * a + a + 4) ^ 2 / 4) - (3 * a * (a + 4)) := by
    calc
      0 ≤ (4 : ℝ) * ((1 + ((-1 / 2) * a)))^2 := by positivity
      _ = ((3 * a + a + 4) ^ 2 / 4) - (3 * a * (a + 4)) := by ring
  exact sub_nonneg.mp h
