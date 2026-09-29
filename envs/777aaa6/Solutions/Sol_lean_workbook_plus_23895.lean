-- Prove2me | solution 1 for lean_workbook_plus_23895
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:16:13.627652+00:00
-- url     : https://prove2.me/submissions/e54a507f-7daa-4633-ac78-e42842742463

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : y = (x^2 + 4)/12) : y = 1/12 * x^2 + 1/3 := by
  (intros; linarith)
