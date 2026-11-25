-- Prove2me | Theorems.Thm_semiprime_iff_prime_mul
-- name    : semiprime_iff_prime_mul
-- status  : Open
-- author  : @mwm
-- created : 2026-11-25T01:29:11.292501+00:00
-- url     : https://prove2.me/theorems/267a9b9c-f6cc-44fe-8956-b9d436f36ac7
-- title:
--   Semiprimes are products of two primes
-- statement:
--   A natural number $n$ is a **semiprime** — that is, it has exactly two prime
--   factors counted with multiplicity, equivalently $\Omega(n) = 2$ — if and only if it factors as a product
--   $n = pq$ of two primes $p$ and $q$.
--
--   Both directions are elementary. If $n = pq$ with $p, q$ prime then $\Omega(n) = \Omega(p) + \Omega(q) = 1 + 1 = 2$.
--   Conversely, if $\Omega(n) = 2$ then the prime factorization list of $n$ has length $2$, say $[p, q]$, and since that
--   list is exactly the multiset of prime factors with $\operatorname{list.prod} = n$, we recover $n = pq$ with both
--   $p$ and $q$ prime. The degenerate case $n = 0$ is excluded by the definition of $\Omega$-almost-primality, and
--   $n = 1$ is excluded because $\Omega(1) = 0 \ne 2$.
--
--   This is the standard bridge between the multiplicative characterization of semiprimes and the predicate used in
--   statements such as **Chen's theorem**, where a large even integer is written as $n = p + q$ with $p$ prime and
--   $q$ either prime or a product of two primes.
-- source:
--   Chen, J. (1973). On the representation of a large even integer as the sum of a prime and the product of at most two primes. Kexue Tongbao 18, 385--386; see also Halberstam--Richert, Sieve Methods, 1974, Chapter 6.

import Mathlib

import Mathlib

theorem semiprime_iff_prime_mul (n : ℕ) :
    Nat.IsSemiprime n ↔ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p * q := by
  sorry
