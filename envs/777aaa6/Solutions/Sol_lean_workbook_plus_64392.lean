-- Prove2me | solution 1 for lean_workbook_plus_64392
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:48:35.516541+00:00
-- url     : https://prove2.me/submissions/ce31eaac-5392-4281-9797-71b5d0c18b3e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (μ_s : ℝ) (h₀ : 0 < a ∧ 0 < b) (h₁ : 0 < μ_s) (h₂ : b / a < μ_s) : b / a < μ_s := by
  (intros; simp_all)
