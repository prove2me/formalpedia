-- Prove2me | solution 1 for lean_workbook_plus_70767
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:22:43.270166+00:00
-- url     : https://prove2.me/submissions/8c3093e0-a49b-47bb-9919-be0538bc5536

import Mathlib.Analysis.Complex.Basic

theorem solution : ∃ k : ℤ, k < 1000 ∧ |k * Real.sqrt 2 - ↑⌊k * Real.sqrt 2⌋| < 1 / 1000 := by
  refine ⟨0, by norm_num, ?_⟩
  simp
