-- Prove2me | solution 1 for lean_workbook_plus_52421
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:04:33.599599+00:00
-- url     : https://prove2.me/submissions/bfacd05b-2aea-421b-9c31-28552f1ceff1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c x y z : ℝ) (h : a = 3 * x ∧ b = 4 * y ∧ c = 5 * z) (hx : x > 0 ∧ y > 0 ∧ z > 0) : a > 0 ∧ b > 0 ∧ c > 0 := by
  (intros; simp_all)
