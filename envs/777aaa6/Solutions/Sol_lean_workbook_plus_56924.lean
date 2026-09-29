-- Prove2me | solution 1 for lean_workbook_plus_56924
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:24:00.350329+00:00
-- url     : https://prove2.me/submissions/388a8596-8546-4906-aa3a-9b231076fc36

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x + y + z - 6) ^ 2 ≥ 0 := by
  (intros; positivity)
