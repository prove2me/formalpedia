-- Prove2me | Theorems.Thm_sexy_prime_conjecture
-- name    : sexy_prime_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T19:08:12.280768+00:00
-- url     : https://prove2.me/theorems/0eaed440-562a-4e71-ad50-f6387d7f494f
-- statement:
--   **Sexy Prime Conjecture**: There are infinitely many sexy primes, i.e., prime pairs $(p, p+6)$.
--
--   Examples: $(5, 11)$, $(7, 13)$, $(11, 17)$, $(13, 19)$, $(23, 29)$, $\ldots$ So named because "sex" is Latin for six. This is a special case of Polignac's conjecture ($k=6$) and Hardy–Littlewood Conjecture A. There are infinitely many sexy prime triplets $(p, p+6, p+12)$ and quadruplets $(p, p+6, p+12, p+18)$ expected as well.
--
--   **Source**: Hardy, G.H., Littlewood, J.E. (1923). Acta Math. 44, 1–70.
-- source:
--   https://en.wikipedia.org/wiki/Sexy_prime

import Mathlib

theorem sexy_prime_conjecture :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 6)}.Infinite := by
  sorry
