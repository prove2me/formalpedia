-- Prove2me | solution 1 for lean_workbook_plus_1680
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:06:42.656124+00:00
-- url     : https://prove2.me/submissions/b1ea8013-4960-45d7-93c5-52f784580e7b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a r : ℝ) (h : |r| < 1) : ∑' i : ℕ, a * r ^ i = a / (1 - r) := by
  rw [tsum_mul_left,tsum_geometric_of_abs_lt_one h]
  ring
