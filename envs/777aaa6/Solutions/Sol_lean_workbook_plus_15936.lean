-- Prove2me | solution 1 for lean_workbook_plus_15936
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:12:43.968294+00:00
-- url     : https://prove2.me/submissions/576308f6-ef81-4a2d-8de2-fd03be788770

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} :
  (a - b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2 + (3 / 2) * (a + b + c) ^ 2 * (a ^ 2 - a * b - a * c + b ^ 2 - b * c + c ^ 2) ^ 2 ≥ 0 := by
  (intros; positivity)
