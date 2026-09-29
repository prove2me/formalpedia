-- Prove2me | solution 1 for lean_workbook_plus_1432
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:33:26.008374+00:00
-- url     : https://prove2.me/submissions/9d081f8c-81fd-4b39-8fc8-45b58813cb88

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (2 * a ^ 2 - 2 * a * b - 2 * a * c + b ^ 2 + c ^ 2) ^ 2 ≥ 0 := by
  (intros; positivity)
