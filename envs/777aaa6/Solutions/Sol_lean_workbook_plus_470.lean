-- Prove2me | solution 1 for lean_workbook_plus_470
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:17:11.569714+00:00
-- url     : https://prove2.me/submissions/fd19caa7-53aa-4e67-8652-67f047368b9e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a d : ℝ) (h : a = 0 ∧ d = 0) : ∑' i : ℕ, (a + i * d) = 0 := by
  (intros; simp_all)
