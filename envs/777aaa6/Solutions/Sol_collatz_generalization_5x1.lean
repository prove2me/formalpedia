-- Prove2me | solution 1 for collatz_generalization_5x1
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:44:12.311037+00:00
-- url     : https://prove2.me/submissions/3371cdda-28e0-4617-add2-7f88191ebe32

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

theorem solution : ¬ (∀ n : ℕ, 1 ≤ n →
    ∃ k : ℕ, (Nat.rec n (fun _ m =>
      if m % 2 = 0 then m / 2 else (5 * m + 1) / 2) k = 1)) := by
  intro h
  let orbit := ({13, 33, 83, 208, 104, 52, 26} : Finset ℕ)
  have hinvariant : ∀ k : ℕ, Nat.rec 13 (fun _ m =>
      if m % 2 = 0 then m / 2 else (5 * m + 1) / 2) k ∈ orbit := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      simp only
      simp only [orbit, Finset.mem_insert, Finset.mem_singleton] at ih
      rcases ih with h | h | h | h | h | h | h <;> rw [h] <;> decide
  obtain ⟨k, hk⟩ := h 13 (by decide)
  have hh := hinvariant k
  rw [hk] at hh
  norm_num [orbit] at hh
