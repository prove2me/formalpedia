-- Prove2me | solution 1 for lean_workbook_plus_19642
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:04:36.19627+00:00
-- url     : https://prove2.me/submissions/b5b72aec-585e-48aa-8e09-06554393d82c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} : (b - c) ^ 2 * (-2 * b + a - 2 * c) ^ 2 + (c - a) ^ 2 * (-2 * c + b - 2 * a) ^ 2 + (a - b) ^ 2 * (-2 * a + c - 2 * b) ^ 2 ≥ 0 := by
  (intros; positivity)
