-- Prove2me | solution 1 for lean_workbook_plus_28717
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:44:18.860823+00:00
-- url     : https://prove2.me/submissions/5af85cd5-de5b-491a-b549-cdf5060a32e0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : a^2+b^2+c^2 ≥ 2*(a+b+c)-3 := by
  intros
  have h : (0 : ℝ) ≤ (a^2+b^2+c^2) - (2*(a+b+c)-3) := by
    calc
      0 ≤ (1 : ℝ) * ((1 + ((-1) * c)))^2 + (1 : ℝ) * ((1 + ((-1) * b)))^2 + (1 : ℝ) * ((1 + ((-1) * a)))^2 := by positivity
      _ = (a^2+b^2+c^2) - (2*(a+b+c)-3) := by ring
  exact sub_nonneg.mp h
