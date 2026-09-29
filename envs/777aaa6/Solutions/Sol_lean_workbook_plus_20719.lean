-- Prove2me | solution 1 for lean_workbook_plus_20719
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:37:15.606826+00:00
-- url     : https://prove2.me/submissions/c6c0b205-d026-4a28-9661-f8e0f6eb4419

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : x ≠ 0 ∧ y ≠ 0) (h₂ : x * x = y * y) : (x + y) * (x + y) + (x - y) * (x - y) - (2 * y) * (2 * y) = 0 := by
  (intros; linarith)
