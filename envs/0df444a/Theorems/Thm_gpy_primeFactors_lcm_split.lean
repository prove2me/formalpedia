-- Prove2me | Theorems.Thm_gpy_primeFactors_lcm_split
-- name    : gpy_primeFactors_lcm_split
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:23:21.05227+00:00
-- url     : https://prove2.me/theorems/1d244a54-5df5-4ecd-9a46-0cdac6797330
-- title:
--   Prime divisors of a least common multiple split by the greatest common divisor
-- statement:
--   For nonzero natural numbers D and E, the prime divisors of lcm D E are exactly the union of the prime divisors of gcd D E, of D / gcd D E, and of E / gcd D E. This is an unconditional elementary lemma.
-- source:
--   GPY monomial joint (GPYMonomialJoint.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_primeFactors_lcm_split {D E : ℕ} (hD0 : D ≠ 0) (hE0 : E ≠ 0) :
    (Nat.lcm D E).primeFactors
      = (Nat.gcd D E).primeFactors ∪ (D / Nat.gcd D E).primeFactors
        ∪ (E / Nat.gcd D E).primeFactors := by sorry
