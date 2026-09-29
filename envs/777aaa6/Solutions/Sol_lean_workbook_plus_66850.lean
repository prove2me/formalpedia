-- Prove2me | solution 1 for lean_workbook_plus_66850
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:14:37.720536+00:00
-- url     : https://prove2.me/submissions/8fb83579-73bb-4445-b7f7-dd4cbb11785f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (A B C : ℝ) (h₁ : A / 3 = B / 4) (h₂ : B / 4 = C / 5) : A / 3 = C / 5 ∧ B / 4 = C / 5 ∧ A / 3 = B / 4 := by
  (intros; simp_all)
