-- Prove2me | solution 1 for lean_workbook_plus_65543
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:50:12.959087+00:00
-- url     : https://prove2.me/submissions/f1155a3d-48f0-479c-a95b-fd9752ee9d0d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c d : ℝ} : 7 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 - 12 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) + (a + b + c + d) * (5 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - 5 * (a ^ 2 * (b + c + d) + b ^ 2 * (c + d + a) + c ^ 2 * (d + a + b) + d ^ 2 * (a + b + c)) + 6 * (b * c * d + a * c * d + a * b * d + a * b * c)) = 2 * ((a - b) ^ 2 * (c - d) ^ 2 + (a - c) ^ 2 * (b - d) ^ 2 + (a - d) ^ 2 * (b - c) ^ 2) := by
  (intros; linarith)
