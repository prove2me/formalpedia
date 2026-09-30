-- Prove2me | solution 1 for lean_workbook_plus_390
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:37:23.537294+00:00
-- url     : https://prove2.me/submissions/79386a95-8f20-4754-9772-65dab89d4318

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem solution (n : ℕ) (a : ℕ → ℕ) (a1 : a 0 = 1)
    (a_rec : ∀ n, a (n + 1) = a n ^ 2 + a n + 1) :
    (a n ^ 2 + 1) ∣ (a (n + 1) ^ 2 + 1) := by
  rw [a_rec n]
  refine ⟨a n ^ 2 + 2 * a n + 2, ?_⟩
  ring

#print axioms solution
