-- Prove2me | solution 1 for lean_workbook_plus_78652
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:01:15.314605+00:00
-- url     : https://prove2.me/submissions/d995c5f7-666a-4c3e-b7cc-80289011238e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ∃ M, ∀ n, |(1 : ℝ) / 2 ^ n| ≤ M := by
  refine ⟨1, fun n => ?_⟩
  rw [abs_of_nonneg (by positivity)]
  exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))

#print axioms solution
