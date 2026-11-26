-- Prove2me | Theorems.Thm_edenic_semiprime_not_perfect
-- name    : edenic_semiprime_not_perfect
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-26T16:48:19.949421+00:00
-- url     : https://prove2.me/theorems/d8b40990-98d0-5f7e-9a77-13a8aaa5384b
-- title:
--   An Edenic semiprime is never a perfect number
-- statement:
--   For every Edenic semiprime $n = p(p+2)$,
--   $$\lnot\, \mathrm{Perfect}(n),$$
--   i.e. $n$ is never a perfect number — never equal to the sum of its proper divisors.
--
--   Write $\sigma(n) = \sum_{d \mid n} d$ for the sum-of-divisors function. Since the twin primes are coprime, $\sigma$ is multiplicative:
--   $$\sigma(n) = \sigma(p)\,\sigma(p+2) = (1+p)\bigl(1+(p+2)\bigr) = (p+1)(p+3) = p^2 + 4p + 3 .$$
--   Perfection would demand $\sigma(n) = 2n = 2p(p+2) = 2p^2 + 4p$, but
--   $$\sigma(n) - 2n = 3 - p^2 \le -6 \qquad (p \ge 3),$$
--   so $\sigma(n) < 2n$ always: the sum of proper divisors falls short of $n$ by exactly $p^2 - 3$. Every Edenic semiprime is therefore not just non-perfect but *deficient* (target `edenic_semiprime_deficient`), with the deficiency $p^2 - 3$ growing without bound along the family ($15$: deficient by $6$; $35$: by $22$; $143$: by $118$).
--
--   **Formalization.** `Nat.perfect_iff_sum_divisors_eq_two_mul` (valid for $0 < n$, supplied by `Nat.mul_pos`) rewrites the assumed perfection; `Nat.Prime.divisors` identifies the divisor set of each prime as $\{1, p\}$ and `Finset.sum_insert`/`Finset.sum_singleton` compute $\sigma(p) = 1 + p$; `Nat.Coprime.sum_divisors_mul` (fed `twin_primes_coprime`, imported) multiplies the two sums into $\sigma(n) = (1+p)(1+(p+2))$; `ring` normalizes both sides of the equality and `omega`, armed with $9 \le p^2$ from `Nat.mul_le_mul`, derives the contradiction.
--
--   **Reuse.** A reduction through `twin_primes_coprime`; the $\sigma$-computation is inlined but matches the statement of `edenic_semiprime_sum_divisors`. Strengthens to `edenic_semiprime_deficient`.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

theorem edenic_semiprime_not_perfect (n : ℕ) (h : IsEdenicSemiprime n) : ¬ Nat.Perfect n := by
  sorry
