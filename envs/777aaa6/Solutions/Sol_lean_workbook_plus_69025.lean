-- Prove2me | solution 1 for lean_workbook_plus_69025
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:04:00.061354+00:00
-- url     : https://prove2.me/submissions/ff29452a-9cce-423b-a2f9-8d3efda404d1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a : ℕ → ℤ) (a0 : a 0 = 0) (a1 : a 1 = -1)
    (a_rec : ∀ m, a (m + 2) = 2 * a (m + 1) - a m) :
    ∃ f : ℤ → ℤ, ∀ m, a m = f m := by
  refine ⟨fun m => -m, ?_⟩
  intro m
  induction m using Nat.twoStepInduction with
  | zero => simpa using a0
  | one => simpa using a1
  | more m ih0 ih1 =>
      rw [a_rec, ih0, ih1]
      push_cast
      ring

#print axioms solution
