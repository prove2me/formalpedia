-- Prove2me | solution 1 for lean_workbook_plus_28764
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:11:43.227961+00:00
-- url     : https://prove2.me/submissions/eb43016a-567a-4696-a926-8339a29c79b4

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000


theorem solution (n : ℕ) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 0) :
  ∀ i, x i = 0 := by
  intro i
  have hq : x i ^ 2 = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j))).mp hx i (Finset.mem_univ i)
  nlinarith [sq_nonneg (x i)]
