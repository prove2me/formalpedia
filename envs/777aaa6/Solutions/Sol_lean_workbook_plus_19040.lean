-- Prove2me | solution 1 for lean_workbook_plus_19040
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:03:47.520718+00:00
-- url     : https://prove2.me/submissions/001d38ac-79cd-4b1c-b04e-be9e96bbf14b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (s : ℝ) (h : s > 6) : 2 * (s - 3) ^ 2 ≥ s ^ 2 - 18 := by
  (intros; nlinarith [sq_nonneg (s)])
