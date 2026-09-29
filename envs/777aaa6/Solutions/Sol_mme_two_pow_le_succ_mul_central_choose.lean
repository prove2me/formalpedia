-- Prove2me | solution 1 for mme_two_pow_le_succ_mul_central_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T11:05:17.988318+00:00
-- url     : https://prove2.me/submissions/64f62f87-ff4c-4a02-8114-98be852c3df6

import Mathlib.Data.Nat.Choose.Sum

open BigOperators Finset

set_option autoImplicit false
set_option warningAsError true

theorem solution (n : ℕ) :
    2 ^ n ≤ (n + 1) * Nat.choose n (n / 2) := by
  rw [← Nat.sum_range_choose]
  calc
    (∑ k ∈ range (n + 1), Nat.choose n k) ≤
        ∑ _k ∈ range (n + 1), Nat.choose n (n / 2) := by
      apply Finset.sum_le_sum
      intro k _hk
      exact Nat.choose_le_middle k n
    _ = (n + 1) * Nat.choose n (n / 2) := by simp
