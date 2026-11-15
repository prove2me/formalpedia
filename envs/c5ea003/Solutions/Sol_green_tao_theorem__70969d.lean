-- Prove2me | solution 1 for green_tao_theorem
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:32:32.847202+00:00
-- url     : https://prove2.me/submissions/f4c0bf56-a9c1-4203-9d33-d22889bf11b2

import Theorems.Thm_GreenTao_green_tao

theorem solution (k : ℕ) (hk : 1 ≤ k) :
    ∃ a d : ℕ, 1 ≤ d ∧ ∀ j : Fin k, Nat.Prime (a + j.val * d) := by
  obtain ⟨a, d, hd, hp⟩ := GreenTao.green_tao k
  refine ⟨a, d, hd, ?_⟩
  intro j
  simpa only [Set.mem_setOf_eq, Nat.mul_comm] using hp j.val j.isLt
