-- Prove2me | solution 1 for lean_workbook_plus_58475
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:45:05.749957+00:00
-- url     : https://prove2.me/submissions/a290a36e-5807-4030-bb27-4a64e9398369

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : y = -x^2/2 - Real.sqrt (x^4/4 + 6*x)) : y = -x^2/2 - Real.sqrt (x^4/4 + 6*x) := by
  (intros; simp_all)
