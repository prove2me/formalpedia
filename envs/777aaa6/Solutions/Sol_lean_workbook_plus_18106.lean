-- Prove2me | solution 1 for lean_workbook_plus_18106
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:56:09.219533+00:00
-- url     : https://prove2.me/submissions/305efc89-83cb-4cac-91f6-058ba81a25a6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x y : ℝ, (x^4+x^2*y^2+y^4)=(x^2+y^2)^2-(x*y)^2 := by
  (intros; linarith)
