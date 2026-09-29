-- Prove2me | solution 1 for lean_workbook_plus_41424
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:39:19.873204+00:00
-- url     : https://prove2.me/submissions/2b191483-d263-46f4-b351-dd2910f7471c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a * b ≥ 1) : a^2 + b^2 ≥ a + b := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
