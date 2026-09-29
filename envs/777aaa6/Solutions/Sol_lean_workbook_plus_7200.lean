-- Prove2me | solution 1 for lean_workbook_plus_7200
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:49:26.232747+00:00
-- url     : https://prove2.me/submissions/d7ca6fbf-bfe9-4d12-a17f-c3453583e7ea

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (y : ℝ) (hy : y > 0) : y^3 < y^3 + 2*y^2 + 1 ∧ y^3 + 2*y^2 + 1 < (y + 1)^3 := by
  (intros; constructor <;> nlinarith [sq_nonneg (y)])
