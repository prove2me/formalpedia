-- Prove2me | solution 1 for lean_workbook_plus_18020
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:55:39.292669+00:00
-- url     : https://prove2.me/submissions/271262cf-d6ac-45f4-ad97-4c906d389330

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a * b * c = 1) : a * b * c = 1 := by
  (intros; simp_all)
