-- Prove2me | solution 1 for lean_workbook_plus_69955
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:30:07.084266+00:00
-- url     : https://prove2.me/submissions/3165e2d4-7c43-476f-8d45-e70b2e365305

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 ≤ x ∧ x < 1) : ⌊x + 2⌋ = 2 := by
  (intros; simp_all)
