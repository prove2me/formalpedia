-- Prove2me | solution 1 for lean_workbook_plus_58457
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:40:02.845042+00:00
-- url     : https://prove2.me/submissions/c50340bb-696c-4202-b0aa-6dfa39503141

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) : (a - b) ^ 2 / a / b * (b - c) ^ 2 / b / c * (c - a) ^ 2 / c / a ≥ 0 := by
  have h : (a - b) ^ 2 / a / b * (b - c) ^ 2 / b / c * (c - a) ^ 2 / c / a
      = ((a - b) * (b - c) * (c - a) * a⁻¹ * b⁻¹ * c⁻¹) ^ 2 := by
    ring
  rw [h]
  exact sq_nonneg _
