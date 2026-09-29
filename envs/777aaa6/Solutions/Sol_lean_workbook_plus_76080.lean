-- Prove2me | solution 1 for lean_workbook_plus_76080
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:20:25.540514+00:00
-- url     : https://prove2.me/submissions/6892c118-58f5-4b1e-942f-bab69100f7fa

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) (n : ℕ) : (a - b) ^ (2 * n) + (b - c) ^ (2 * n) + (c - a) ^ (2 * n) ≥ 0 := by
  simp only [pow_mul]
  positivity
