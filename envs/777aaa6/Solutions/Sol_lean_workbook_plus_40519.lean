-- Prove2me | solution 1 for lean_workbook_plus_40519
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:40:12.898114+00:00
-- url     : https://prove2.me/submissions/dfa21ce6-15cf-4498-b705-228c12475cb0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x^2 * y^2 + y^2 * z^2 + z^2 * x^2 ≥ x^2 * y * z + x * y^2 * z + x * y * z^2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
