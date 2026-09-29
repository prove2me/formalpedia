-- Prove2me | solution 1 for lean_workbook_plus_8416
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:58:35.057622+00:00
-- url     : https://prove2.me/submissions/143a0999-777f-4e9f-ac88-e7dc2c72815a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 2 * (a * b + b * c + c * a) - a ^ 2 - b ^ 2 - c ^ 2 > 0 := by
  (intros; nlinarith)
