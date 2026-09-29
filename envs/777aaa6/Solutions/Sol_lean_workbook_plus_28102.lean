-- Prove2me | solution 1 for lean_workbook_plus_28102
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:05:55.855685+00:00
-- url     : https://prove2.me/submissions/dcaf8698-3e3d-43c9-a9ef-ebe2c5d4843a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (h₁ : 20 + 0.4 * (x - 60) ≥ 28) (h₂ : 20 + 0.4 * (x - 60) ≤ 40) : 80 ≤ x ∧ x ≤ 110 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x)])
