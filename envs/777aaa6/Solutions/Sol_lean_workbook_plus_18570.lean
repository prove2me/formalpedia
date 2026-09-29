-- Prove2me | solution 1 for lean_workbook_plus_18570
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:57:00.54162+00:00
-- url     : https://prove2.me/submissions/9fe83480-df31-4e53-916e-10b921a20ec2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : 9 - x^2 ≥ 0) :
  -3 ≤ x ∧ x ≤ 3 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x)])
