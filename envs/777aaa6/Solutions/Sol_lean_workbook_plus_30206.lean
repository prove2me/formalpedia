-- Prove2me | solution 1 for lean_workbook_plus_30206
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:43:15.79843+00:00
-- url     : https://prove2.me/submissions/21675b1f-cc0a-480f-becf-00013f8dc058

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (y z : ℝ) : (y^2 + z^2) * (1^2 + 1^2) ≥ (y + z)^2 := by
  (intros; nlinarith [sq_nonneg (y), sq_nonneg (z), sq_nonneg (y - z), sq_nonneg (y + z)])
