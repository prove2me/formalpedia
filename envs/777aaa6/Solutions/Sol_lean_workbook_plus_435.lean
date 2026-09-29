-- Prove2me | solution 1 for lean_workbook_plus_435
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:18.807701+00:00
-- url     : https://prove2.me/submissions/88fadd3e-2abd-45e6-8e40-b5361cec6d85

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a^2 + b^2 - c^2) * (a - b)^2 + (b^2 + c^2 - a^2) * (b - c)^2 + (c^2 + a^2 - b^2) * (c - a)^2 ≥ 0 := by
  intros
  
  have h_identity : ((a^2 + b^2 - c^2) * (a - b)^2 + (b^2 + c^2 - a^2) * (b - c)^2 + (c^2 + a^2 - b^2) * (c - a)^2) - (0) = (2 : ℝ) * 1 * (((a ^ 2) + ((-1 / 2) * (b ^ 2)) + ((-1 / 2) * (c ^ 2)) + (b * c) + ((-1 / 2) * a * b) + ((-1 / 2) * a * c)))^2 + ((3 / 2) : ℝ) * 1 * (((c ^ 2) + ((-1) * (b ^ 2)) + (a * b) + ((-1) * a * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a^2 + b^2 - c^2) * (a - b)^2 + (b^2 + c^2 - a^2) * (b - c)^2 + (c^2 + a^2 - b^2) * (c - a)^2) - (0) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
