-- Prove2me | solution 1 for lean_workbook_plus_19881
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:06:09.22075+00:00
-- url     : https://prove2.me/submissions/c6df44dc-1a7e-4667-88a1-52033d051d74

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ a b : ℝ, a ≥ 0 ∧ b ≥ 0 →
  Real.sqrt ((a + b) / 2) ≥ (Real.sqrt a + Real.sqrt b) / 2 := by
  intro a b ⟨ha, hb⟩
  have hsa := Real.sqrt_nonneg a
  have hsb := Real.sqrt_nonneg b
  have hsa2 := Real.sq_sqrt ha
  have hsb2 := Real.sq_sqrt hb
  rw [ge_iff_le, Real.le_sqrt (by positivity)]
  · nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b)]
  · positivity
