-- Prove2me | Theorems.Thm_edenic_semiprime_gcd_sigma
-- name    : edenic_semiprime_gcd_sigma
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T23:06:44.6128+00:00
-- url     : https://prove2.me/theorems/cd5454ed-8d24-4d71-9faa-2199a3458ed7
-- title:
--   An Edenic semiprime is coprime to its divisor sum, except 15
-- statement:
--   For every Edenic semiprime $n = p(p+2)$,
--   $$\gcd\bigl(n,\ \sigma(n)\bigr) = 1 \qquad\text{or}\qquad n = 15 .$$
--
--   By `edenic_semiprime_sum_divisors`, $\sigma(n) = (p+1)(p+3)$. Suppose a prime $q$ divides both $n = p(p+2)$ and $\sigma(n) = (p+1)(p+3)$ (`Nat.Prime.not_coprime_iff_dvd`). Since $q \mid p(p+2)$ with $q$ prime, either:
--   - $q = p$: then $p \mid (p+1)(p+3)$, so $p \mid p+1$ (impossible) or $p \mid p+3$, i.e. $p \mid 3$, so $p = 3$ and $n = 15$;
--   - $q = p+2$: then $(p+2) \mid (p+1)(p+3)$, so $(p+2) \mid p+1$ or $(p+2) \mid p+3$ — both give $(p+2) \mid 1$, impossible.
--
--   Hence the only common-prime case is $p = 3$, i.e. $n = 15$, where indeed $\gcd(15, \sigma(15)) = \gcd(15, 24) = 3 \neq 1$. For all other members ($35, 143, 323, \dots$) $n$ and $\sigma(n)$ are coprime. This is the "coprimality exception" pattern seen elsewhere in the family (cf. `edenic_semiprime_mod_six`'s exception at 15).
--
--   **Formalization.** Reduction to `edenic_semiprime_sum_divisors`; the non-coprime branch extracts a common prime via `Nat.Prime.not_coprime_iff_dvd`, splits $q$ against both factors of $n$ with `Nat.Prime.dvd_mul`/`Nat.Prime.dvd_iff_eq`, and eliminates the impossible sub-branches with `Nat.dvd_sub` (producing a divisor of $1$ or of $3$).
--
--   **Reuse.** Reduction to `edenic_semiprime_sum_divisors`. Classifies exactly when $n$ and $\sigma(n)$ share a factor — never, except the minimal member $15$.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_sum_divisors

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_sum_divisors

theorem edenic_semiprime_gcd_sigma (n : ℕ) (h : IsEdenicSemiprime n) :
    n.Coprime (∑ d ∈ n.divisors, d) ∨ n = 15 := by
  sorry
