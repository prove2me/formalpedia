-- Prove2me | solution 1 for lean_workbook_plus_76064
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:00:51.297568+00:00
-- url     : https://prove2.me/submissions/840ca3cc-3945-4c3d-ad5e-924513d1b0a8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a : ℕ → ℕ) (a0 : a 0 = 0) (a1 : a 1 = 2)
    (a_rec : ∀ n, n ≥ 2 → a n + a (n - 2) = 2 * (a (n - 1) + 1)) :
    ∃ f : ℕ → ℕ, ∀ n, a n = f n := by
  refine ⟨fun n => n * (n + 1), ?_⟩
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simpa using a0
  | one => simpa using a1
  | more n ih0 ih1 =>
      have h := a_rec (n + 2) (by omega)
      rw [show n + 2 - 2 = n by omega, show n + 2 - 1 = n + 1 by omega,
        ih0, ih1] at h
      dsimp only at h ⊢
      nlinarith

#print axioms solution
