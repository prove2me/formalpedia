-- Prove2me | Theorems.Thm_congruent_numbers_exact
-- name    : congruent_numbers_exact
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T03:25:58.45606+00:00
-- url     : https://prove2.me/theorems/d232682f-f139-48f7-8d62-d11d75cb171d
-- statement:
--   Congruent number problem: n is congruent iff the elliptic curve y² = x³ - n²x has a rational point of infinite order. Tunnell (1983) gave a criterion under BSD. Whether every squarefree n ≡ 5,6,7 (mod 8) is congruent remains open.
-- source:
--   https://en.wikipedia.org/wiki/Congruent_number

import Mathlib

import Mathlib

theorem congruent_numbers_exact :
    ∀ n : ℕ, 1 ≤ n →
    ((∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧
      a * b / 2 = n) ↔
    (∃ x y : ℚ, y ^ 2 = x ^ 3 - (n : ℚ) ^ 2 * x ∧ y ≠ 0)) := by
  sorry
