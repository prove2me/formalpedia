-- Prove2me | solution 1 for lean_workbook_plus_32240
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:18:05.480997+00:00
-- url     : https://prove2.me/submissions/89cedaa0-6e0c-4534-bd3d-08124a8e86ee

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x z : ℂ) : x^2 = 2 * z * (x^2 / 9 + 1) ↔ x^2 = 2 * z * (x^2 / 9 + 1) := by
  norm_num
