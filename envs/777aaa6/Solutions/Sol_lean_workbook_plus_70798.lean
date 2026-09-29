-- Prove2me | solution 1 for lean_workbook_plus_70798
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:51:08.709398+00:00
-- url     : https://prove2.me/submissions/c26480bc-17e1-4af4-b3f9-19cbf586bc20

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h : ∃ a b c : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ (a * 1 + b * 6 + c * 2 = 0 ∧ a * 5 + b * 2 + c * 1 = 0 ∧ a * 1 + b * 0 + c * (-2) = 0)) : ∃ a b c : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ (a * 1 + b * 6 + c * 2 = 0 ∧ a * 5 + b * 2 + c * 1 = 0 ∧ a * 1 + b * 0 + c * (-2) = 0) := by
  (intros; simp_all)
