-- Prove2me | solution 1 for lean_workbook_plus_14395
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:30:36.996868+00:00
-- url     : https://prove2.me/submissions/79191252-268e-4133-a34c-366e0d65c97f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x ∈ Set.Icc 3 9) : 3 ≤ x ∧ x ≤ 9 := by
  (intros; simp_all)
