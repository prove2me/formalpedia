-- Prove2me | solution 1 for lean_workbook_plus_19983
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:04:59.196561+00:00
-- url     : https://prove2.me/submissions/f5d9b3af-b2f2-4dbe-9298-9083930b6828

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (y : ℝ) (h : y > 2) : y^4 < y^4 + 4 * y + 1 ∧ y^4 + 4 * y + 1 < (y^2 + 1)^2 := by
  (intros; constructor <;> nlinarith [sq_nonneg (y)])
