-- Prove2me | solution 1 for lean_workbook_plus_15427
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:27:29.21543+00:00
-- url     : https://prove2.me/submissions/f9d80b2c-8aae-4810-ae8e-a5cd1f02a3aa

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (hab : a + b + c = 0) : a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 + 6 * a * b * c ≥ -3 := by
  have hc : c = -a-b := by linarith
  rw [hc]
  nlinarith [sq_nonneg (a^2+a*b-b-1), sq_nonneg (b^2+a*b-a-1), sq_nonneg ((a-1)*(b-1))]
