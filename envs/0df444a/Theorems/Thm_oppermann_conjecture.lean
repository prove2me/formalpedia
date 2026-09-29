-- Prove2me | Theorems.Thm_oppermann_conjecture
-- name    : oppermann_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:26:17.286549+00:00
-- url     : https://prove2.me/theorems/b39da3ff-1b3f-4b81-ac39-23ee77adde32
-- statement:
--   **Oppermann's Conjecture**: For every integer $x \geq 2$, there is a prime in each of $(x(x-1), x^2)$ and $(x^2, x(x+1))$.
--
--   For $x=4$: interval $(12,16)$ contains $13$; interval $(16,20)$ contains $17,19$.
--
--   Proposed by Oppermann (1882). Stronger than Legendre's conjecture. Implies prime gaps satisfy $p_{n+1} - p_n < 2\sqrt{p_n}$. AlphaProof proved it for sufficiently large $x$ assuming bounded prime gaps.
-- source:
--   https://en.wikipedia.org/wiki/Oppermann%27s_conjecture

import Mathlib

theorem oppermann_conjecture (x : ℕ) (hx : 2 ≤ x) :
    (∃ p ∈ Finset.Ioo (x * (x - 1)) (x ^ 2), Nat.Prime p) ∧
    (∃ p ∈ Finset.Ioo (x ^ 2) (x * (x + 1)), Nat.Prime p) := by
  sorry
