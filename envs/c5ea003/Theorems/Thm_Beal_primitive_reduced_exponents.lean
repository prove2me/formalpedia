-- Prove2me | Theorems.Thm_Beal_primitive_reduced_exponents
-- name    : Beal.primitive_reduced_exponents
-- status  : Open
-- author  : @Wenqian Xing
-- created : 2026-09-06T03:50:26.190549+00:00
-- url     : https://prove2.me/theorems/a6dc5fc2-9d2d-452e-b256-8ad54e41c2da
-- title:
--   Beal conjecture for ordered exponents $4$ or odd primes
-- statement:
--   Let $a,b,c$ be positive, pairwise coprime integers. Let $p,q,r$ each be either $4$ or an odd prime. Suppose $p\le q$ and at least one of $p,q,r$ is prime. Then
--
--   $$a^p+b^q\ne c^r.$$
--
--   This is the explicitly restricted open case of Beal's conjecture: the ordering removes the symmetry of the two summands, and the prime condition excludes the settled signature $(4,4,4)$. An accompanying proved exponent-normalization lemma and a fourth-power argument reduce the full conjecture to this statement. No restriction is imposed on the sizes of the remaining odd primes.
-- source:
--   R. Daniel Mauldin, A Generalization of Fermat's Last Theorem: The Beal Conjecture and Prize Problem, Notices AMS 44(11), 1997, p. 1436, equation and primitive formulation, https://www.ams.org/notices/199711/beal.pdf; restricted exponent case and elementary normalization proved in the accompanying reduction, using Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f, Mathlib/Data/Nat/Factors.lean, Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt. This normalization is not claimed as a separately numbered result in Mauldin.

import Mathlib.Data.Nat.Factors

theorem Beal.primitive_reduced_exponents {a b c p q r : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hp : p = 4 ∨ Nat.Prime p ∧ Odd p)
    (hq : q = 4 ∨ Nat.Prime q ∧ Odd q)
    (hr : r = 4 ∨ Nat.Prime r ∧ Odd r)
    (hpq : p ≤ q)
    (hprime : Nat.Prime p ∨ Nat.Prime q ∨ Nat.Prime r)
    (hab : a.Coprime b) (hac : a.Coprime c) (hbc : b.Coprime c) :
    a ^ p + b ^ q ≠ c ^ r := by sorry
