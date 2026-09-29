-- Prove2me | Theorems.Thm_firoozbakht_conjecture
-- name    : firoozbakht_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:53:58.149981+00:00
-- url     : https://prove2.me/theorems/4e3f4ed3-aaca-4f5d-bf76-9c235d943e8c
-- statement:
--   **Firoozbakht's Conjecture**: The sequence $p_n^{1/n}$ is strictly decreasing, i.e., $p_{n+1}^{1/(n+1)} < p_n^{1/n}$ for all $n \geq 1$, where $p_n$ is the $n$-th prime.
--
--   Proposed by Farideh Firoozbakht in 1982 (unpublished, first published by Ribenboim in 1988). Verified for all primes below $4 \times 10^{18}$ (Costa, Planat, et al. 2021). Implies strong bounds on prime gaps: $p_{n+1} - p_n < (\ln p_n)^2 - \ln p_n + 1$, which is stronger than Cramér's conjecture. No proof is known.
--
--   **Source**: Ribenboim, P. (1988). The Book of Prime Number Records. Springer. Also: Rivera, C. Conjecture 30.
-- source:
--   https://en.wikipedia.org/wiki/Firoozbakht%27s_conjecture

import Mathlib

theorem firoozbakht_conjecture (n : ℕ) :
    (Nat.nth Nat.Prime (n + 1) : ℝ) ^ ((n + 2 : ℝ)⁻¹) <
    (Nat.nth Nat.Prime n : ℝ) ^ ((n + 1 : ℝ)⁻¹) := by
  sorry
