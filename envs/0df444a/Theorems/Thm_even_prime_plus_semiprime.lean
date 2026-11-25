-- Prove2me | Theorems.Thm_even_prime_plus_semiprime
-- name    : even_prime_plus_semiprime
-- status  : Open
-- author  : @mwm
-- created : 2026-11-25T01:29:10.71023+00:00
-- url     : https://prove2.me/theorems/da86e598-bb99-48a7-9fc2-15580888d4e5
-- title:
--   Arbitrarily large even integers are a prime plus a semiprime
-- statement:
--   For every bound $N$ there is an even integer $m \ge N$ admitting a representation
--   $m = p + q$ where $p$ is prime and $q$ is a semiprime. Equivalently, infinitely many even integers are the sum of a
--   prime and a semiprime.
--
--   Fix the semiprime $q = 9 = 3 \cdot 3$. For every prime $p > 2$ the number $m = p + 9$ is even (odd plus odd), is at
--   least as large as any prescribed bound once $p$ is large enough, and is of the required form. Since the primes are
--   unbounded, such $m$ exists above every $N$.
--
--   This is the *infinitude* shadow of **Chen's theorem**, which asserts the far stronger statement that *every*
--   sufficiently large even integer has such a representation. The version proved here keeps the representation shape
--   prime + semiprime but drops "all sufficiently large" to "infinitely many", which is what makes it elementary.
-- source:
--   Chen, J. (1973), Kexue Tongbao 18, 385--386; Halberstam--Richert, Sieve Methods, 1974, Chapter 6.

import Mathlib

import Mathlib

theorem even_prime_plus_semiprime (n : ℕ) :
    ∃ m : ℕ, Even m ∧ n ≤ m ∧ ∃ p q : ℕ, p.Prime ∧ Nat.IsSemiprime q ∧ m = p + q := by
  sorry
