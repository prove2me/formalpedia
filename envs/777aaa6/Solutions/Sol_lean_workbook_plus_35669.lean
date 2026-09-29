-- Prove2me | solution 1 for lean_workbook_plus_35669
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:42:51.615897+00:00
-- url     : https://prove2.me/submissions/230d2717-e665-4e81-a04a-0a40d3dd69a2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a * (3 * a - b + c) + b * (3 * b - c + a) + c * (3 * c - a + b) = 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  (intros; linarith)
