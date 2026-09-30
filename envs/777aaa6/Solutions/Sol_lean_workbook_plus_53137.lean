-- Prove2me | solution 1 for lean_workbook_plus_53137
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:40:26.825251+00:00
-- url     : https://prove2.me/submissions/dbce34c4-8fee-4792-ac45-d508ee9b4e27

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) (hx : 1 < x) : ∃ p, x < p ∧ p < 2 * x := by
  refine ⟨3 * x / 2, ?_, ?_⟩ <;> linarith
