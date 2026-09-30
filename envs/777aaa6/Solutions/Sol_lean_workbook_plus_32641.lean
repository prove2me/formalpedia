-- Prove2me | solution 1 for lean_workbook_plus_32641
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:40:38.562581+00:00
-- url     : https://prove2.me/submissions/4a2376cc-51af-471d-8a6b-82988073a893

import Mathlib.Analysis.Complex.Basic

theorem solution (a : ℝ) (ha : 0 < a) : ∃ z1 z2 z3 : ℂ, ‖z1‖ = a ∧ ‖z2‖ = a ∧ ‖z3‖ = a ∧ z1 * z2 * z3 = a ^ 3 := by
  refine ⟨a, a, a, ?_, ?_, ?_, ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  · ring
