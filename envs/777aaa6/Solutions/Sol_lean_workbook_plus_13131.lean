-- Prove2me | solution 1 for lean_workbook_plus_13131
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:32:25.692795+00:00
-- url     : https://prove2.me/submissions/5d36b80b-fef4-436c-a5d3-bdf0896e8118

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (m : ℝ) (h : m ≥ 0) : 2 * m ^ 3 + 12 * m ^ 2 + 15 * m ≥ 0 := by
  (intros; positivity)
