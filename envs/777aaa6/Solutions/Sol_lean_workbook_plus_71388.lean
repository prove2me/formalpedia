-- Prove2me | solution 1 for lean_workbook_plus_71388
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:34:50.927712+00:00
-- url     : https://prove2.me/submissions/bea793b3-37c9-4ac1-90e9-681b69214ccf

import Mathlib

theorem solution (f : ℝ → ℝ) (m : ℝ) (hf : ∀ x, -1 ≤ f x ∧ f x ≤ 1) :
    ∃ M, ∀ x, |f (x + m) - f x| ≤ M := by
  refine ⟨2, fun x => abs_le.mpr ?_⟩
  constructor <;> linarith [(hf (x + m)).1, (hf (x + m)).2, (hf x).1, (hf x).2]

#print axioms solution
