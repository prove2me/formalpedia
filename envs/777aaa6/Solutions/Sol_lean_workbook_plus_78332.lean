-- Prove2me | solution 1 for lean_workbook_plus_78332
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:46:44.993559+00:00
-- url     : https://prove2.me/submissions/3f839839-fef6-46b8-9bd2-7f1f3dd49310

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (p : ℂ) : ∃ y, y ^ 3 - 3 * p * y + p ^ 3 + 1 = 0 := by
  refine ⟨-(p + 1), ?_⟩
  ring

#print axioms solution
