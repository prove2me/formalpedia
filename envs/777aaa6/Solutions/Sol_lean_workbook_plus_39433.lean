-- Prove2me | solution 1 for lean_workbook_plus_39433
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:41:34.275105+00:00
-- url     : https://prove2.me/submissions/ba80d097-8325-4394-9a99-8535a2c19b00

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x + y + 2 * z) ^ 2 ≥ 4 * (y + z) * (x + z) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
