-- Prove2me | solution 2 for lean_workbook_plus_49896
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:30:55.814568+00:00
-- url     : https://prove2.me/submissions/416c7f88-a29b-4f20-aaf4-78254a22e0d2

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) : |4*x + 3| - |x + 5| ≤ 8 ↔ -16/5 ≤ x ∧ x ≤ 10/3 := by
  simp only [abs_eq_max_neg,max_def]
  split_ifs <;> constructor <;> intro h <;> (try constructor) <;> linarith
