-- Prove2me | solution 1 for lean_workbook_plus_73173
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:50:00.988715+00:00
-- url     : https://prove2.me/submissions/5cc9570f-0c76-4cae-be5c-5513ea12c144

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem solution (n : ℕ) (f : ℕ → ℕ)
    (h : ∀ n, f (n + 2) = f n + f (n + 1)) :
    (f n)^2 + (f (n + 4))^2 =
      (f (n + 1))^2 + 4 * (f (n + 2))^2 + (f (n + 3))^2 := by
  have h3 : f (n + 3) = f (n + 1) + f (n + 2) := by
    simpa [Nat.add_assoc] using h (n + 1)
  have h4 : f (n + 4) = f (n + 2) + f (n + 3) := by
    simpa [Nat.add_assoc] using h (n + 2)
  rw [h4, h3, h n]
  ring

#print axioms solution
