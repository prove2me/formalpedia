-- Prove2me | solution 1 for lean_workbook_plus_25045
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:27:34.970589+00:00
-- url     : https://prove2.me/submissions/7ba87636-30cd-440f-bab6-e46d14414a07

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p : ℝ) (hp : p > 0 ∧ p < 1) (h : 2 / 11 < p ∧ p < 3 / 11) : 2 / 11 < p ∧ p < 3 / 11 := by
  (intros; simp_all)
