-- Prove2me | solution 1 for lean_workbook_plus_38906
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:05:05.00745+00:00
-- url     : https://prove2.me/submissions/d514893b-e5ce-4803-8b17-68801b760a17

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (t : ℝ) (ht : t > 0) : (t - 1/t)^2 ≥ 0 := by
  (intros; positivity)
