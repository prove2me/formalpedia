-- Prove2me | solution 1 for lean_workbook_plus_81335
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:37:39.046151+00:00
-- url     : https://prove2.me/submissions/461475af-47bb-4ada-806f-a36764e9c676

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) : c < a + b := by
  (intros; simp_all)
