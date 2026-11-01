-- Prove2me | Theorems.Thm_gpy_primeFactors_gcd_disjoint_left
-- name    : gpy_primeFactors_gcd_disjoint_left
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T01:58:05.729839+00:00
-- url     : https://prove2.me/theorems/d68e8c06-e6d1-44eb-b4f8-5608d7869e05
-- title:
--   Disjointness of the gcd part and the D-only part for squarefree D
-- statement:
--   For squarefree D, the prime divisors of gcd D E are disjoint from the prime divisors of D / gcd D E: a common prime would square-divide D. This is an unconditional elementary lemma.
-- source:
--   GPY monomial joint (GPYMonomialJoint.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_primeFactors_gcd_disjoint_left {D E : ℕ} (hsqD : Squarefree D) :
    Disjoint (Nat.gcd D E).primeFactors (D / Nat.gcd D E).primeFactors := by sorry
