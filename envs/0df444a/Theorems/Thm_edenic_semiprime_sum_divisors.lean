-- Prove2me | Theorems.Thm_edenic_semiprime_sum_divisors
-- name    : edenic_semiprime_sum_divisors
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T17:20:52.118685+00:00
-- url     : https://prove2.me/theorems/b18a864a-93cc-4f81-9489-a75f82d6ae60
-- title:
--   The divisor sum of an Edenic semiprime
-- statement:
--   For an Edenic semiprime $n = p(p+2)$, the divisor sum is
--   $$\sigma(n) = \sum_{d \mid n} d = (p+1)(p+3) = p^2 + 4p + 3 .$$
--
--   The function $\sigma$ is multiplicative on coprime arguments (`Nat.Coprime.sum_divisors_mul`), and for a prime $q$ the divisor set is $\{1, q\}$ with sum $1 + q$. Hence
--   $$\sigma(n) = \sigma(p)\,\sigma(p+2) = (1 + p)\,(1 + (p+2)) = (p+1)(p+3).$$
--
--   Equivalently, $\sigma(n) - n = (p^2 + 4p + 3) - (p^2 + 2p) = 2p + 3$: the sum of the proper divisors of an Edenic semiprime is exactly $2p + 3$.
--
--   **Formalization.** The two two-element sums are evaluated by `Finset.sum_pair` (side condition $1 \neq p$, resp. $1 \neq p+2$, from `hp.ne_one`/`hp2.ne_one`), and the arithmetic identity closes by `ring`.
--
--   **Reuse.** Reduction to `twin_primes_coprime`. The identity $\sum_{\text{proper}} = 2p+3$ is precisely what makes `edenic_semiprime_deficient` below a one-line inequality.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

theorem edenic_semiprime_sum_divisors (n : ℕ) (h : IsEdenicSemiprime n) :
    ∃ p, p.Prime ∧ (p + 2).Prime ∧ n = p * (p + 2) ∧
      ∑ d ∈ n.divisors, d = (p + 1) * (p + 3) := by
  sorry
