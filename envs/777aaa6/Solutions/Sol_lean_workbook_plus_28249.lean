-- Prove2me | solution 1 for lean_workbook_plus_28249
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:33:08.030326+00:00
-- url     : https://prove2.me/submissions/5aece328-6d31-4d54-aaf3-6a02ea0a4ed5

import Mathlib

theorem power_decomposition (n : Nat) :
    exists q : Nat, 5 ^ n = 16 * q + 4 * n + 1 := by
  induction n with
  | zero => exact ⟨0, by decide⟩
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨5 * q + n, ?_⟩
    rw [pow_succ, hq]
    ring

theorem solution (n : Nat) (hn : 1 ≤ n) : 16 ∣ (5 ^ n - 4 * n + 15) := by
  obtain ⟨q, hq⟩ := power_decomposition n
  refine ⟨q + 1, ?_⟩
  omega

#print axioms solution
