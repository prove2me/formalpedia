-- Prove2me | solution 1 for lean_workbook_plus_61745
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:19:50.650424+00:00
-- url     : https://prove2.me/submissions/33731485-b384-4eb3-9668-be829c6c80d7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (m n : ℝ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : 1 ≤ m * n) : 1 / m + 1 / n ≥ 16 / (1 + 8 * m * n) := by
  (intros; field_simp; nlinarith [sq_nonneg (m), sq_nonneg (n), sq_nonneg (m - n), sq_nonneg (m + n)])
