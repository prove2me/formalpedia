-- Prove2me | solution 1 for lean_workbook_plus_14370
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:23.812976+00:00
-- url     : https://prove2.me/submissions/1de25cd8-0a21-430b-b234-0945dc992200

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2+1)*(b^2+1)*(c^2+1) ≥ (a+b)*(b+c)*(c+a) := by
  intros
  have h : (0 : ℝ) ≤ ((a^2+1)*(b^2+1)*(c^2+1)) - ((a+b)*(b+c)*(c+a)) := by
    calc
      0 ≤ (1 : ℝ) * ((1 + ((-1) * a * b * c)))^2 + ((1 / 2) : ℝ) * ((c + ((-1) * b * c)))^2 + ((1 / 2) : ℝ) * ((c + ((-1) * a * c)))^2 + ((1 / 2) : ℝ) * ((b + ((-1) * b * c)))^2 + ((1 / 2) : ℝ) * ((b + ((-1) * a * b)))^2 + ((1 / 2) : ℝ) * ((a + ((-1) * a * c)))^2 + ((1 / 2) : ℝ) * ((a + ((-1) * a * b)))^2 := by positivity
      _ = ((a^2+1)*(b^2+1)*(c^2+1)) - ((a+b)*(b+c)*(c+a)) := by ring
  exact sub_nonneg.mp h
