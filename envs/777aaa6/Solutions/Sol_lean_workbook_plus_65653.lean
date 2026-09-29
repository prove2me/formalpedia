-- Prove2me | solution 1 for lean_workbook_plus_65653
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:30.270289+00:00
-- url     : https://prove2.me/submissions/a17fe1c3-eff0-44f0-80db-b0e5ecb1a449

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) (habc : a + b + c = 3) (ha : a > 0 ∧ b > 0 ∧ c > 0): a + b + c >= 3 / 2 := by
  (intros; simp_all)
