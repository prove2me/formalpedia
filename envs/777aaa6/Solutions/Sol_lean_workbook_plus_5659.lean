-- Prove2me | solution 1 for lean_workbook_plus_5659
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:07:22.637429+00:00
-- url     : https://prove2.me/submissions/2b8791ae-c08d-40d0-971c-15a9c8c767a2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (y z : ℝ) : 2 * y ^ 2 + 2 * z ^ 2 ≥ 4 * y * z := by
  (intros; nlinarith [sq_nonneg (y), sq_nonneg (z), sq_nonneg (y - z), sq_nonneg (y + z)])
