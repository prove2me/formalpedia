-- Prove2me | solution 1 for lean_workbook_plus_72938
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:21:33.178923+00:00
-- url     : https://prove2.me/submissions/9be27c61-458f-4082-bbc0-7bdf9541c308

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p : ℝ) (h : p^2 = 1 + p) : p^3 = 1 + 2 * p := by
  (intros; nlinarith [sq_nonneg (p)])
