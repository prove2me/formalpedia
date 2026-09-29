-- Prove2me | solution 1 for lean_workbook_plus_10449
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:50:23.020036+00:00
-- url     : https://prove2.me/submissions/80f0a900-b758-43f1-9458-c17249d84ae8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℤ) (h1 : ∃ x : ℤ, x^2 = a/2 + 1) (h2 : ∃ y : ℤ, y^2 = a/3) : ∃ x y : ℤ, x^2 = a/2 + 1 ∧ y^2 = a/3 := by
  (intros; simp_all)
