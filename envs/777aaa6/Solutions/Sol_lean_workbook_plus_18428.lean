-- Prove2me | solution 1 for lean_workbook_plus_18428
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:56:44.549156+00:00
-- url     : https://prove2.me/submissions/c9e1bf61-f9a0-44d2-8f4f-f0423a4d40aa

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} :
  (1 / 126) * (21 * a ^ 2 + 7 * a * b - 17 * a * c - 21 * b ^ 2 + 10 * b * c) ^ 2 + (1 / 126) * (-17 * a * b + 10 * a * c + 21 * b ^ 2 + 7 * b * c - 21 * c ^ 2) ^ 2 + (1 / 126) * (-21 * a ^ 2 + 10 * a * b + 7 * a * c - 17 * b * c + 21 * c ^ 2) ^ 2 + (263 / 9198) * (7 * a * b - 17 * a * c + 10 * b * c) ^ 2 + (263 / 9198) * (-17 * a * b + 10 * a * c + 7 * b * c) ^ 2 + (263 / 9198) * (10 * a * b + 7 * a * c - 17 * b * c) ^ 2 ≥ 0 := by
  (intros; positivity)
