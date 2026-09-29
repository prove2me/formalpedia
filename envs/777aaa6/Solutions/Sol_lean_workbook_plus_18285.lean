-- Prove2me | solution 1 for lean_workbook_plus_18285
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:56:28.688986+00:00
-- url     : https://prove2.me/submissions/287e0b60-a706-4693-9126-0beed6a27698

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x^2 * y^2 + 1 + (x - y)^2) / (x - y)^2 + (y^2 * z^2 + 1 + (y - z)^2) / (y - z)^2 + (z^2 * x^2 + 1 + (z - x)^2) / (z - x)^2 ≥ 9 / 2 ↔ (x^2 + y^2 + (x * y - 1)^2) / (x - y)^2 + (y^2 + z^2 + (y * z - 1)^2) / (y - z)^2 + (z^2 + x^2 + (z * x - 1)^2) / (z - x)^2 ≥ 9 / 2 := by
  (intros; ring)
