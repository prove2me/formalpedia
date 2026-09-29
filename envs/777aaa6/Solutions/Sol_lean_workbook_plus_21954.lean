-- Prove2me | solution 1 for lean_workbook_plus_21954
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:45:11.646445+00:00
-- url     : https://prove2.me/submissions/3fab8bd2-c352-4d94-9840-08da8577a4f3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a + b > c ∧ b + c > a ∧ a + c > b := by
  (intros; simp_all)
