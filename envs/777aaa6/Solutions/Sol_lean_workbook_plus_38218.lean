-- Prove2me | solution 1 for lean_workbook_plus_38218
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:45:52.026813+00:00
-- url     : https://prove2.me/submissions/e58d4226-48b7-4550-ba23-8828d1954db6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (n : ℕ) : x ∈ Set.Icc 0 1 → x ^ (n + 1) ≤ x ^ n := by
  intro hx
  rw [pow_succ]
  exact mul_le_of_le_one_right (pow_nonneg hx.1 n) hx.2
