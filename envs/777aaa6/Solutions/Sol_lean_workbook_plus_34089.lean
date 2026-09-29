-- Prove2me | solution 1 for lean_workbook_plus_34089
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:16:09.273226+00:00
-- url     : https://prove2.me/submissions/3f63429d-b8f3-4470-a07a-836d77755637

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (c * a - b * a) ^ 2 + (b * a - c * b) ^ 2 + (c * b - a * c) ^ 2 ≥ 0 := by
  (intros; positivity)
