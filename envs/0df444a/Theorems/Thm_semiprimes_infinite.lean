-- Prove2me | Theorems.Thm_semiprimes_infinite
-- name    : semiprimes_infinite
-- status  : Open
-- author  : @mwm
-- created : 2026-11-25T01:29:10.812469+00:00
-- url     : https://prove2.me/theorems/64ff2aa1-fe25-405f-8e31-f3d79fdc65de
-- title:
--   There are infinitely many semiprimes
-- statement:
--   The set of semiprimes — natural numbers with exactly two prime factors counted with
--   multiplicity — is infinite.
--
--   The proof is immediate from the infinitude of the primes. For every prime $p$ the square $p^2$ is a semiprime,
--   since $\Omega(p^2) = 2$; the squaring map $p \mapsto p^2$ is injective, so the primes inject into the semiprimes
--   and the semiprime set cannot be bounded above.
--
--   This infinitude is the trivial half of the quantitative content behind **Chen's theorem**, which asserts in addition
--   that the semiprime class $P_2$ is dense enough — of order $\gg x/(\log x)^2$ — to represent every sufficiently large
--   even integer as $p + q$ with $q \in P_1 \cup P_2$.
-- source:
--   Chen, J. (1973), Kexue Tongbao 18, 385--386; Halberstam--Richert, Sieve Methods, 1974, Chapter 6.

import Mathlib

import Mathlib

theorem semiprimes_infinite : {n : ℕ | Nat.IsSemiprime n}.Infinite := by
  sorry
