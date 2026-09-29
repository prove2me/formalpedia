-- Prove2me | solution 1 for lean_workbook_plus_59669
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:33:58.113696+00:00
-- url     : https://prove2.me/submissions/5b0c38aa-1bfe-477d-aec2-c8cbedb1a5fb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (y z : ℝ) : (y^2 + z^2) / 2 ≥ (y + z) ^ 2 / 4 := by
  (intros; nlinarith [sq_nonneg (y), sq_nonneg (z), sq_nonneg (y - z), sq_nonneg (y + z)])
