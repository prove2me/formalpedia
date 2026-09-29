-- Prove2me | Theorems.Thm_cramer_conjecture
-- name    : cramer_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:53:20.998502+00:00
-- url     : https://prove2.me/theorems/007775e7-6efa-40a8-bfa2-580bb3063f8c
-- statement:
--   **Cramér's Conjecture**: The maximal prime gap satisfies $\limsup_{n \to \infty} (p_{n+1} - p_n) / (\ln p_n)^2 = 1$, where $p_n$ denotes the $n$-th prime.
--
--   Equivalently (and as stated here): for every $\varepsilon > 0$, all sufficiently large prime gaps satisfy $p_{n+1} - p_n < (1+\varepsilon)(\ln p_n)^2$. Proposed by Harald Cramér (1936) based on probabilistic heuristics modeling primes as random sets with density $1/\ln n$. The best known upper bound is $O(p_n^{0.525})$ (Baker-Harman-Pintz, 2001). The conjecture implies much tighter bounds than all known results.
--
--   **Source**: Cramér, H. (1936). On the order of magnitude of the difference between consecutive prime numbers. Acta Arithmetica, 2, 23–46.
-- source:
--   https://en.wikipedia.org/wiki/Cram%C3%A9r%27s_conjecture

import Mathlib

theorem cramer_conjecture (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      let p := (Nat.nth Nat.Prime n : ℝ)
      let q := (Nat.nth Nat.Prime (n + 1) : ℝ)
      q - p < (1 + ε) * Real.log p ^ 2 := by
  sorry
