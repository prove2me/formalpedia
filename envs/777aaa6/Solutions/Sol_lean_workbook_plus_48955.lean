-- Prove2me | solution 1 for lean_workbook_plus_48955
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:37:23.527608+00:00
-- url     : https://prove2.me/submissions/e90116cc-c7a9-42aa-b047-887501767f38

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℝ, ∀ x_1 : ℝ, ∀ x_2 : ℝ, ∀ x_3 : ℝ, ∀ x_4 : ℝ, x_1 + x_2 + x_3 + x_4 + (1 - x_1 - x_2 - x_3 - x_4) = 1 ∧ x_1^2 + x_2^2 + x_3^2 + x_4^2 + (1 - x_1 - x_2 - x_3 - x_4)^2 ≤ 1 / 4 → x_1^2 - x_1 * (1 - x_2 - x_3 - x_4) + x_2^2 + x_3^2 + x_4^2 - x_2 - x_3 - x_4 + x_2 * x_3 + x_2 * x_4 + x_3 * x_4 + 3 / 8 ≤ 0 := by
  (intros; linarith)
