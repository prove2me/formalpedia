-- Prove2me | solution 1 for lean_workbook_plus_16111
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:20:55.336161+00:00
-- url     : https://prove2.me/submissions/cdf6ccef-ee60-4906-8503-577324d9fe9c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : (x^4 / (1 + x^2)) ≥ 0 := by
  (intros; positivity)
