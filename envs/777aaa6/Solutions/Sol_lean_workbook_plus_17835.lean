-- Prove2me | solution 1 for lean_workbook_plus_17835
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:51.910712+00:00
-- url     : https://prove2.me/submissions/d2db1c67-5096-4870-bce8-e2c3fd78ce91

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) : (3 * a * b * c + a ^ 3 + b ^ 3 + c ^ 3) * (a + b + c) ≥ 2 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a) := by
  intros
  
  have h_identity : ((3 * a * b * c + a ^ 3 + b ^ 3 + c ^ 3) * (a + b + c)) - (2 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a)) = (1 : ℝ) * 1 * (((a ^ 2) + ((-1 / 2) * (b ^ 2)) + ((-1 / 2) * (c ^ 2)) + (b * c) + ((-1 / 2) * a * b) + ((-1 / 2) * a * c)))^2 + ((3 / 4) : ℝ) * 1 * (((c ^ 2) + ((-1) * (b ^ 2)) + (a * b) + ((-1) * a * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((3 * a * b * c + a ^ 3 + b ^ 3 + c ^ 3) * (a + b + c)) - (2 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
