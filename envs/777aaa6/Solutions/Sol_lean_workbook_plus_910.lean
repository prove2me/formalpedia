-- Prove2me | solution 1 for lean_workbook_plus_910
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:25:48.041806+00:00
-- url     : https://prove2.me/submissions/70f4e547-d035-4a2d-8506-9d8b7b462db8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} : (1 / 2) * ((a - b) ^ 2 * (a + b - c) ^ 2 + (b - c) ^ 2 * (b + c - a) ^ 2 + (c - a) ^ 2 * (c + a - b) ^ 2) ≥ 0 := by
  (intros; positivity)
