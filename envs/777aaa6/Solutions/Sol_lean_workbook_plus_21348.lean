-- Prove2me | solution 1 for lean_workbook_plus_21348
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:46:18.889088+00:00
-- url     : https://prove2.me/submissions/b4d28236-bf59-407f-b779-ca34fce30d3e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : (x^4 - 2 * x^3 + x^2 - 2 * x + 1)^2 * (x^2 + 2 * (x - 1)^2 * (x^2 + 1)) ≥ 0 := by
  (intros; positivity)
