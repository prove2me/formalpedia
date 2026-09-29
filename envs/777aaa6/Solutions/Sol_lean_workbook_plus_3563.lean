-- Prove2me | solution 1 for lean_workbook_plus_3563
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:17:04.081458+00:00
-- url     : https://prove2.me/submissions/e19145ff-f22e-4488-9867-a0e2c74cf305

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : (x^2 + 2)^2 ≥ 4 * (x^2 + 1) := by
  (intros; nlinarith [sq_nonneg (x)])
