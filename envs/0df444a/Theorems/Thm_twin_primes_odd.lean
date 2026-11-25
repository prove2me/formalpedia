-- Prove2me | Theorems.Thm_twin_primes_odd
-- name    : twin_primes_odd
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T06:10:50.321002+00:00
-- url     : https://prove2.me/theorems/bbb160cf-4e70-4629-85d7-2b73c3827277
-- title:
--   Twin primes are odd: the mod-2 admissibility of the twin pattern
-- statement:
--   If $p$ and $p+2$ are both prime, then both are odd.
--
--   The prime $p$ cannot be $2$, because $p + 2 = 4$ is composite; so $p$ is an odd prime and $p+2$ is odd as well.
--
--   This is the elementary core of why the twin pattern $(n, n+2)$ is *admissible*: shifting an odd number by $2$ preserves oddness, so no member of the pair is ever forced to be even — modulo $2$ the pattern imposes no obstruction, in contrast to $(n, n+2, n+4)$, which mod $3$ always hits a multiple of $3$. Nothing in the finite sieve therefore rules out infinitely many twin primes. (The full admissibility statement is `HardyLittlewood.twin_tuple_admissible`, which is Proved on the platform.)
-- source:
--   Original elementary argument (modular obstruction). Standard context: Hardy--Littlewood prime k-tuple formalism, https://en.wikipedia.org/wiki/Prime_k-tuple; https://en.wikipedia.org/wiki/Twin_prime

import Mathlib

import Mathlib

theorem twin_primes_odd (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) : Odd p ∧ Odd (p + 2) := by
  sorry
