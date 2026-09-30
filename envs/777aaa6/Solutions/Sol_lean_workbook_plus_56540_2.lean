-- Prove2me | solution 2 for lean_workbook_plus_56540
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:23:08.677767+00:00
-- url     : https://prove2.me/submissions/4be66df0-9db8-4957-88d7-cca25785c686

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : x ≠ 0) (h₂ : x * y * (x^2 - y^2) = x^2 + y^2): x^2 + y^2 >= 0 := by
  (intros; positivity)
