-- Prove2me | solution 1 for lean_workbook_plus_77776
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:02:44.268284+00:00
-- url     : https://prove2.me/submissions/d40bfba0-056d-44c4-a45d-dce65a0dba23

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c k : ℝ) (h₁ : a ≥ b ∧ b ≥ c) (h₂ : 0 ≤ k) : a^3 + b^3 + c^3 + 3 * a * b * c - (a * b * (a + b) + b * c * (b + c) + c * a * (c + a) + k * (a^2 + b^2 + c^2 - a * b - b * c - c * a)) = (a + b - 2 * c) * (a - b)^2 + (1 / 2) * (c - k) * ((a - b)^2 + (b - c)^2 + (c - a)^2) := by
  (intros; linarith)
