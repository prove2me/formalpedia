-- Prove2me | solution 1 for lean_workbook_plus_80078
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:00:26.039124+00:00
-- url     : https://prove2.me/submissions/79f84a52-c679-466f-a26a-eba120d9c159

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a x y : ℝ) (h : x = y) : a * x = a * y := by
  (intros; simp_all)
