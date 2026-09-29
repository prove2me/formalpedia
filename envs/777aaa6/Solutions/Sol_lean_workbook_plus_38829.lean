-- Prove2me | solution 1 for lean_workbook_plus_38829
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:54:06.18659+00:00
-- url     : https://prove2.me/submissions/74a902e5-086d-41df-953e-68659bdfd8fc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) : (a - c) ^ 2 + (b - d) ^ 2 ≥ 0 := by
  (intros; positivity)
