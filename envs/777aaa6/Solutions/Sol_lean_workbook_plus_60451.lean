-- Prove2me | solution 1 for lean_workbook_plus_60451
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:45:10.768688+00:00
-- url     : https://prove2.me/submissions/38c02c9c-49a5-4642-96c1-12759d7f48ae

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0 := by
  (intros; positivity)
