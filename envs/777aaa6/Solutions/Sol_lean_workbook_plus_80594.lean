-- Prove2me | solution 1 for lean_workbook_plus_80594
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:01:15.883329+00:00
-- url     : https://prove2.me/submissions/a8b4f607-dab4-4576-8ce4-757963dd8e7a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : x > 0) (hy : y > 0) : (x + y) / 2 ≥ 2 * x * y / (x + y) ↔ 1 / (x + y) ≤ 1 / 4 * (1 / x + 1 / y) := by
  (intros; field_simp; ring)
