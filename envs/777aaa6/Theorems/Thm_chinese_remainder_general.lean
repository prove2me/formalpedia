-- Prove2me | Theorems.Thm_chinese_remainder_general
-- name    : chinese_remainder_general
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T03:41:14.19251+00:00
-- url     : https://prove2.me/theorems/d0c2859a-2559-4595-a70a-8ffa823be433
-- statement:
--   Chinese Remainder Theorem: For pairwise coprime moduli, the system of congruences x ≡ aᵢ (mod mᵢ) has a unique solution modulo m₁·...·mₙ. Proved. Generalizations to non-coprime moduli and rings are active research.
-- source:
--   https://en.wikipedia.org/wiki/Chinese_remainder_theorem

import Mathlib

import Mathlib

theorem chinese_remainder_general (n : ℕ) (hn : 2 ≤ n)
    (moduli : Fin n → ℕ)
    (hpairwise : ∀ i j : Fin n, i ≠ j → Nat.Coprime (moduli i) (moduli j))
    (remainders : Fin n → ℕ) :
    ∃ x : ℕ, ∀ i : Fin n, x % moduli i = remainders i % moduli i := by
  sorry
