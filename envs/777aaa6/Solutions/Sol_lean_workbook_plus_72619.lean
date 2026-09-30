-- Prove2me | solution 1 for lean_workbook_plus_72619
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:47:18.929213+00:00
-- url     : https://prove2.me/submissions/47813b66-963d-4152-9a23-387d312e0fee

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (a b : ℝ) : a * b = b * a := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg a, sq_nonneg b]
