-- Prove2me | solution 1 for lean_workbook_plus_9733
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:23.018005+00:00
-- url     : https://prove2.me/submissions/3969939f-43d5-416d-ae9f-aa57e6cd1cd7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x^4 + y^4 + z^4 + 2 * x^2 * y^2 + 2 * y^2 * z^2 + 2 * z^2 * x^2) ≥ 3 * x * y * z * (x + y + z) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
