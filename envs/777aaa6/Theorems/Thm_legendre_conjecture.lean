-- Prove2me | Theorems.Thm_legendre_conjecture
-- name    : legendre_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:25:39.2373+00:00
-- url     : https://prove2.me/theorems/285da9f5-f305-4a4d-960b-354c0eb38e27
-- statement:
--   **Legendre's Conjecture**: For every positive integer $n$, there is a prime $p$ with $n^2 < p < (n+1)^2$.
--
--   Examples: between $1$ and $4$: primes $\{2,3\}$; between $4$ and $9$: $\{5,7\}$; between $9$ and $16$: $\{11,13\}$.
--
--   One of Landau's four problems (1912). Ingham (1937) showed it follows from the Riemann Hypothesis. AlphaProof (DeepMind, 2025) proved it conditionally assuming bounded prime gaps.
-- source:
--   https://en.wikipedia.org/wiki/Legendre%27s_conjecture

import Mathlib

theorem legendre_conjecture :
    ∀ n : ℕ, 1 ≤ n → ∃ p ∈ Set.Ioo (n ^ 2) ((n + 1) ^ 2), Nat.Prime p := by
  sorry
