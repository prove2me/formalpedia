-- Prove2me | solution 1 for lean_workbook_plus_29419
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:45:50.930516+00:00
-- url     : https://prove2.me/submissions/078b9fe4-f9ee-4628-b5fc-0ad88856e480

import Mathlib.Analysis.Complex.Basic

theorem solution (x₁ x₂ : ℝ) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) : (1 / x₁ + 2 / (x₁ + x₂)) < 2 * (1 / x₁ + 1 / x₂) := by
  have h1 : 2 / (x₁ + x₂) < 2 / x₂ := by
    apply div_lt_div_of_pos_left (by norm_num) hx₂ (by linarith)
  have h2 : 0 < 1 / x₁ := by positivity
  have h3 : 2 / x₂ = 2 * (1 / x₂) := by ring
  linarith
