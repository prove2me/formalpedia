-- Prove2me | solution 1 for lean_workbook_plus_71794
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:20:39.279951+00:00
-- url     : https://prove2.me/submissions/0bfc500a-38e2-423c-896d-2073352ee1f2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a < b + c ∧ b < a + c ∧ c < a + b := by
  (intros; simp_all)
