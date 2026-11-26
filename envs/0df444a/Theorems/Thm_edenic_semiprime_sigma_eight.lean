-- Prove2me | Theorems.Thm_edenic_semiprime_sigma_eight
-- name    : edenic_semiprime_sigma_eight
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T23:06:41.620665+00:00
-- url     : https://prove2.me/theorems/d7ae974e-f6a7-4f46-801a-1ff3e1be1c63
-- title:
--   The divisor sum of an Edenic semiprime is divisible by 8
-- statement:
--   For every Edenic semiprime $n = p(p+2)$,
--   $$8 \mid \sigma(n) = \sum_{d \mid n} d .$$
--
--   By `edenic_semiprime_sum_divisors`, $\sigma(n) = (p+1)(p+3)$. The prime $p$ is odd, so $p \equiv 1, 3, 5, 7 \pmod 8$ and the product of the two consecutive even numbers $p+1$ and $p+3$ is:
--   - $p \equiv 1$: $2 \cdot 4 = 8 \equiv 0$;
--   - $p \equiv 3$: $4 \cdot 6 = 24 \equiv 0$;
--   - $p \equiv 5$: $6 \cdot 8 = 48 \equiv 0$;
--   - $p \equiv 7$: $8 \cdot 10 = 80 \equiv 0$.
--
--   In every case one of the two factors is divisible by 4 and the other by 2 (among any two consecutive even numbers, one is $2 \pmod 4$ and one is $0 \pmod 4$), so their product is divisible by 8. Equivalently: $\sigma(n) = (p+1)(p+3) = (p+2)^2 - 1$, one less than an odd square, and odd squares are $1 \pmod 8$.
--
--   **Formalization.** Reduction to `edenic_semiprime_sum_divisors`; then oddness of $p$ (via `Nat.Prime.eq_two_or_odd'` after excluding $p = 2$) plus a four-way `omega` split on $p \bmod 8$, each branch reduced by `simp [Nat.mul_mod, Nat.add_mod]`.
--
--   **Reuse.** Reduction to `edenic_semiprime_sum_divisors`. Together with `edenic_semiprime_deficient` ($\sigma(n) - n = 2p+3 < n$) this pins $\sigma(n)$ modulo 8 for every member of the family.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_sum_divisors

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_sum_divisors

theorem edenic_semiprime_sigma_eight (n : ℕ) (h : IsEdenicSemiprime n) :
    (∑ d ∈ n.divisors, d) % 8 = 0 := by
  sorry
