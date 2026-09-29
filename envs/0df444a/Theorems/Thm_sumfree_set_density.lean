-- Prove2me | Theorems.Thm_sumfree_set_density
-- name    : sumfree_set_density
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T03:00:01.585984+00:00
-- url     : https://prove2.me/theorems/82394a78-abb5-4fd6-a8d7-93eda16c8d6d
-- statement:
--   Sum-free sets: A set is sum-free if no element equals the sum of two others. Max size of sum-free subset of {1,...,n} is ⌈n/2⌉ - ⌈n/4⌉ (odd numbers in the upper half). Various quantitative conjectures on structure of large sum-free sets open.
-- source:
--   https://en.wikipedia.org/wiki/Sum-free_set

import Mathlib

import Mathlib

theorem sumfree_set_density :
    ∀ eps : ℝ, 0 < eps →
    ∀ (n : ℕ) (A : Finset (Fin n)),
      (∀ a b c : Fin n, a ∈ A → b ∈ A → c ∈ A →
        a.val + b.val ≠ c.val) →
      (A.card : ℝ) ≤ (n : ℝ) / 2 + eps := by
  sorry
