-- Prove2me | solution 1 for lean_workbook_plus_6672
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:49:39.058516+00:00
-- url     : https://prove2.me/submissions/d9814ede-b66f-4dec-9c62-f27a30a47fbb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (y : ℝ) : y^2 * (y^2 - y + 1) + 3 * (y - 1)^2 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (y)])
