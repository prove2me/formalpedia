-- Prove2me | Theorems.Thm_Goldbach_chebyshev_convolution_extract_prime_pair
-- name    : Goldbach.chebyshev_convolution_extract_prime_pair
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T01:48:12.414754+00:00
-- url     : https://prove2.me/theorems/f6e22ac4-539d-407d-9621-1b2e04032815
-- title:
--   Extract a prime pair using Chebyshev bounds for squares and higher powers
-- statement:
--   For every natural number N at least 4, write
--   R(N) = sum_{m=0}^N Lambda(m) Lambda(N-m).
--   If
--   R(N) > 2 log N [log 4 sqrt(N) + 2 N^(1/3) log N],
--   then there are primes p and q with N = p+q.
--
--   Mathlib's Chebyshev identity expresses the total von Mangoldt weight of
--   non-primes through N as psi(N)-theta(N), equivalently the sum of theta(N^(1/k))
--   over exponents k from 2 through floor(log N/log 2). Isolate the square term
--   and apply the existing bound theta(x) <= log 4*x. For all remaining k at least
--   3, N^(1/k) <= N^(1/3). Bounding their number by log N/log 2 and using
--   log 4 = 2 log 2 gives
--   psi(N)-theta(N) <= log 4 sqrt(N) + 2 N^(1/3) log N.
--
--   Every convolution summand with at least one non-prime endpoint is charged to
--   that endpoint's von Mangoldt weight times log N. Reflecting m to N-m bounds
--   the total unwanted weight by twice the preceding bound times log N. If
--   there is no prime pair, this unwanted weight is the entire convolution,
--   contradicting the hypothesis.
--
--   This is a closed elementary extraction interface in Mathlib revision
--   777aaa61dcd2a1258d2b4962dbe983ede4d23b2e. It reuses Mathlib's known Chebyshev
--   results and does not claim a new theorem about prime distribution. Its leading
--   error has size sqrt(N)*log N; the additional cube-root term is lower order.
--   It is not asserted to dominate the earlier integer-square-root criterion at
--   every small N. No uniform lower bound for R(N), exhaustive finite Goldbach
--   verification, or proof of strong Goldbach is supplied by this theorem.
-- source:
--   An elementary extraction interface for https://prove2.me/missions/The_Goldbach_Conjecture. Reuses Mathlib NumberTheory/Chebyshev psi_eq_theta_add_sum_theta, theta_le_log4_mul_x and psi_sub_theta_eq_sum_not_prime in the pinned revision; no literature novelty or uniform binary-correlation lower bound is claimed.

import Mathlib.NumberTheory.Chebyshev
open scoped BigOperators
set_option autoImplicit false

theorem Goldbach.chebyshev_convolution_extract_prime_pair (N : ℕ) (hN4 : 4 ≤ N)
    (hlarge : (2 * (Real.log 4 * Real.sqrt N + 2 * (N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N) * Real.log N) <
      ∑ m ∈ Finset.range (N+1),
        ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt (N-m)) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ N = p+q := by sorry
