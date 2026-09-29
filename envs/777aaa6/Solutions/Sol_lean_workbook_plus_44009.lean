-- Prove2me | solution 1 for lean_workbook_plus_44009
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:28:35.353846+00:00
-- url     : https://prove2.me/submissions/436af964-c2bb-4bfc-a7e8-2d62884d3ad1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c x y z : ℝ) : x = c * (3 * a ^ 2 - 6 * a * b - b ^ 2) ∧ y = c * (b ^ 2 - 2 * a * b - 3 * a ^ 2) ∧ z = c * (3 * a ^ 2 + b ^ 2) ↔ x = c * (3 * a ^ 2 - 6 * a * b - b ^ 2) ∧ y = c * (b ^ 2 - 2 * a * b - 3 * a ^ 2) ∧ z = c * (3 * a ^ 2 + b ^ 2) := by
  norm_num
