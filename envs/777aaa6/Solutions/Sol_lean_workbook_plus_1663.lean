-- Prove2me | solution 1 for lean_workbook_plus_1663
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:32:53.303812+00:00
-- url     : https://prove2.me/submissions/5b44c032-913d-4c86-a79a-230cc7747bf4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x + y + z) ^ 2 ≥ 3 * (x*y + y*z + z*x) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
