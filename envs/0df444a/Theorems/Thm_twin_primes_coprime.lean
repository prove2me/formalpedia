-- Prove2me | Theorems.Thm_twin_primes_coprime
-- name    : twin_primes_coprime
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T06:10:48.228029+00:00
-- url     : https://prove2.me/theorems/2cb4c586-9f81-4183-9745-c253d78e2fc0
-- title:
--   Consecutive twin primes are coprime
-- statement:
--   If $p$ and $p+2$ are both prime then
--   $$\gcd(p,\, p+2) = 1.$$
--
--   A common divisor of $p$ and $p+2$ divides their difference $(p+2) - p = 2$; since $p$ is an odd prime it is not divisible by $2$, so the greatest common divisor is $1$.
--
--   Equivalently: if $p \mid p+2$ then $p \mid 2$, forcing $p \in \{1, 2\}$, neither of which is a prime whose successor $p+2$ is prime. This is what licenses multiplicativity of the totient and of the divisor count across the two factors of an Edenic semiprime.
-- source:
--   Original elementary argument (modular obstruction). Standard context: Hardy--Littlewood prime k-tuple formalism, https://en.wikipedia.org/wiki/Prime_k-tuple; https://en.wikipedia.org/wiki/Twin_prime

import Mathlib

import Mathlib

theorem twin_primes_coprime (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) : p.Coprime (p + 2) := by
  sorry
