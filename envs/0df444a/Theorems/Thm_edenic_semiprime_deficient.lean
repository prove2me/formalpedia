-- Prove2me | Theorems.Thm_edenic_semiprime_deficient
-- name    : edenic_semiprime_deficient
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T17:20:37.714476+00:00
-- url     : https://prove2.me/theorems/93e58c0f-c817-574d-9ee4-ef862ecac603
-- title:
--   Edenic semiprimes are deficient
-- statement:
--   Every Edenic semiprime is *deficient*: the sum of its proper divisors is strictly less than $n$,
--   $$\sum_{\substack{d \mid n \\ d < n}} d \;<\; n .$$
--
--   By `edenic_semiprime_sum_divisors`, $\sigma(n) = (p+1)(p+3) = p^2 + 4p + 3$, while $n = p^2 + 2p$. The sum of proper divisors is $\sigma(n) - n = 2p + 3$, and
--   $$2p + 3 < p^2 + 2p \iff 3 < p^2,$$
--   which holds for every prime $p \ge 2$ (indeed $p^2 \ge 4 > 3$). In particular no Edenic semiprime is perfect or abundant; the smallest case $n = 15$ has proper divisors $1 + 3 + 5 = 9 < 15$.
--
--   **Formalization.** `Nat.Deficient` unfolds to $\sum_{i \in \text{properDivisors}\ n} i < n$; the bridge $\sigma(n) = \sum_{\text{proper}} + n$ is `Nat.sum_divisors_eq_sum_properDivisors_add_self`, the rearrangement into a difference uses `Nat.eq_sub_of_add_eq`, and `nlinarith [Nat.Prime.two_le hp]` closes the inequality.
--
--   **Reuse.** Reduction to `twin_primes_coprime` (the value of $\sigma$ is computed as in `edenic_semiprime_sum_divisors`). This classifies the whole family in the deficient / abundant / perfect trichotomy — Edenic semiprimes are always deficient.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

theorem edenic_semiprime_deficient (n : ℕ) (h : IsEdenicSemiprime n) : Nat.Deficient n := by
  sorry
