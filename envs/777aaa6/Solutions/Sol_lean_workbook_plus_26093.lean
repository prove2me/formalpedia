-- Prove2me | solution 1 for lean_workbook_plus_26093
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:26:23.38336+00:00
-- url     : https://prove2.me/submissions/fa57706d-a1c8-445a-b57f-f1e678b03a0c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : y = -Real.sqrt (x + 1 / 4) + 1 / 2) : y = -Real.sqrt (x + 1 / 4) + 1 / 2 := by
  (intros; simp_all)
