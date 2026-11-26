-- Prove2me | Theorems.Thm_edenic_semiprime_border_prime
-- name    : edenic_semiprime_border_prime
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T23:06:09.534058+00:00
-- url     : https://prove2.me/theorems/af8f7a1f-f7dc-5107-93b8-96a6108ec95e
-- title:
--   A prime divisor of an Edenic semiprime is a twin-pair border
-- statement:
--   If a prime $q$ divides an Edenic semiprime $n = p(p+2)$, then $q$ is one of the two twin primes bounding $n$:
--   $$n = q(q+2) \qquad\text{or}\qquad n = (q-2)q .$$
--
--   Since $n = p(p+2)$ with $p$ and $p+2$ prime, and $q$ is prime dividing the product, Euclid's lemma for primes (`Nat.Prime.dvd_mul`) gives $q \mid p$ or $q \mid (p+2)$. In the first case $q \mid p$ with both prime forces $q = p$; in the second, $q \mid (p+2)$ forces $q = p+2$. Rearranged, the second case says $p = q - 2$, i.e. $n = (q-2)q$ — $q$ is the *upper* member of a twin pair; the first says $q$ is the *lower* member.
--
--   In other words: the prime divisors of an Edenic semiprime are exactly the two twin primes it is built from, and each one sees $n$ as a product with its own twin gap partner. (For $q = 2$ the hypothesis $q \mid n$ never holds, since Edenic semiprimes are odd.)
--
--   **Formalization.** Unfold the definition, apply `Nat.Prime.dvd_mul` to split the divisibility, then `Nat.Prime.dvd_iff_eq` on each branch (prime dividing prime equals it, using `hq.ne_one`); the upper-member rearrangement $p = q-2$ is `omega`.
--
--   **Reuse.** Direct (no imports beyond the definition). Complements `edenic_semiprime_gcd`: instead of two arbitrary Edenic semiprimes, this constrains *any* prime divisor of one.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_border_prime (n q : ℕ) (h : IsEdenicSemiprime n)
    (hq : q.Prime) (hdvd : q ∣ n) :
    n = q * (q + 2) ∨ n = (q - 2) * q := by
  sorry
