-- Prove2me | solution 1 for lean_workbook_plus_52105
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:14:25.261586+00:00
-- url     : https://prove2.me/submissions/24d7467b-9a5b-40c9-ad37-0ef546abcac6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (h : a * b * c = 1) : a ^ 2 + b ^ 2 + c ^ 2 + 3 ≥ 2 * (a + b + c) := by
  intros
  
  have h_identity : (a ^ 2 + b ^ 2 + c ^ 2 + 3) - (2 * (a + b + c)) = (1 : ℝ) * 1 * ((1 + ((-1) * a)))^2 + (1 : ℝ) * 1 * ((1 + ((-1) * b)))^2 + (1 : ℝ) * 1 * ((1 + ((-1) * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (a ^ 2 + b ^ 2 + c ^ 2 + 3) - (2 * (a + b + c)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
