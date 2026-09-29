-- Prove2me | solution 1 for lean_workbook_plus_14173
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:30:22.483743+00:00
-- url     : https://prove2.me/submissions/f8178beb-de39-48ec-85f1-d7644737f5bc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : 0 < a ∧ 0 < b ∧ 0 < c) (habc : a * b * c = 1) (h : Real.sqrt (a * b * c) ≤ 1) : a * b * c ≤ 1 := by
  (intros; simp_all)
