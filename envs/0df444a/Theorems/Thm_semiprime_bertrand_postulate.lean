-- Prove2me | Theorems.Thm_semiprime_bertrand_postulate
-- name    : semiprime_bertrand_postulate
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T01:29:10.432413+00:00
-- url     : https://prove2.me/theorems/9acd9d28-e02a-450c-af9f-4e167201538d
-- title:
--   Bertrand's postulate for semiprimes
-- statement:
--   For every integer $n \ge 2$ there exists a semiprime $m$ in the interval
--   $(n, 2n]$.
--
--   This is a semiprime analogue of **Bertrand's postulate** (proved by Chebyshev, and in Mathlib as
--   `Nat.exists_prime_lt_and_le_two_mul`). The argument transfers directly: applying Bertrand to $\lfloor n/2 \rfloor$
--   produces a prime $p$ with $\lfloor n/2 \rfloor < p \le 2\lfloor n/2 \rfloor \le n$, and then $m = 2p$ satisfies
--   $n < m \le 2n$ while being a product of the two primes $2$ and $p$, hence a semiprime.
--
--   Read as a statement about the distribution of the semiprime set $P_2$, it says $P_2$ intersects every interval of the
--   form $(n, 2n]$ — a much stronger multiplicative-density statement than the corresponding fact for primes, and one
--   that holds for the same elementary reason.
-- source:
--   Chebyshev (1852); analogue of Bertrand's postulate, cf. Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., Theorem 4.14.

import Mathlib

import Mathlib

theorem semiprime_bertrand_postulate (n : ℕ) (hn : 2 ≤ n) :
    ∃ m : ℕ, n < m ∧ m ≤ 2 * n ∧ Nat.IsSemiprime m := by
  sorry
