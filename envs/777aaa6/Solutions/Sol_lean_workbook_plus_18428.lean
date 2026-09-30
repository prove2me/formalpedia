-- Prove2me | solution 1 for lean_workbook_plus_18428
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:08:33.216609+00:00
-- url     : https://prove2.me/submissions/33dfde07-f28e-456f-a389-218993aedf18

import Mathlib.Analysis.Complex.Basic

theorem solution {a b c : ℝ} :
  (1 / 126) * (21 * a ^ 2 + 7 * a * b - 17 * a * c - 21 * b ^ 2 + 10 * b * c) ^ 2 + (1 / 126) * (-17 * a * b + 10 * a * c + 21 * b ^ 2 + 7 * b * c - 21 * c ^ 2) ^ 2 + (1 / 126) * (-21 * a ^ 2 + 10 * a * b + 7 * a * c - 17 * b * c + 21 * c ^ 2) ^ 2 + (263 / 9198) * (7 * a * b - 17 * a * c + 10 * b * c) ^ 2 + (263 / 9198) * (-17 * a * b + 10 * a * c + 7 * b * c) ^ 2 + (263 / 9198) * (10 * a * b + 7 * a * c - 17 * b * c) ^ 2 ≥ 0 := by
  positivity
