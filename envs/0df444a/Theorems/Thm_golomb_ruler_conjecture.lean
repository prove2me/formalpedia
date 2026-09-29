-- Prove2me | Theorems.Thm_golomb_ruler_conjecture
-- name    : golomb_ruler_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T03:00:37.695452+00:00
-- url     : https://prove2.me/theorems/67b107e3-ef21-48f5-8d42-3ef793a4f58d
-- statement:
--   Golomb ruler conjecture: A Golomb ruler of order n (all pairwise differences distinct) can have length ≤ n². Perfect Golomb rulers (length = C(n,2)) exist for n ≤ 4. Optimal lengths for large n are unknown; computed up to order 27.
-- source:
--   https://en.wikipedia.org/wiki/Golomb_ruler

import Mathlib

import Mathlib

theorem golomb_ruler_conjecture (n : ℕ) (hn : 1 ≤ n) :
    ∃ (ruler : Finset ℕ),
      ruler.card = n ∧
      ∀ a b c d : ℕ, a ∈ ruler → b ∈ ruler → c ∈ ruler → d ∈ ruler →
        a ≠ b → c ≠ d → (a - b : ℤ) = (c - d : ℤ) → a = c ∧ b = d ∧
      ∀ m : ℕ, m ∈ ruler → m ≤ n ^ 2 := by
  sorry
