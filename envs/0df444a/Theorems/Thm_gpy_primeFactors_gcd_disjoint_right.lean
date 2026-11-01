-- Prove2me | Theorems.Thm_gpy_primeFactors_gcd_disjoint_right
-- name    : gpy_primeFactors_gcd_disjoint_right
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T02:27:37.961215+00:00
-- url     : https://prove2.me/theorems/446796c5-4cea-4b4d-a9e5-ed55ea57b843
-- title:
--   Disjointness of the combined gcd/D-only part from the E-only part
-- statement:
--   For squarefree D and E, the prime divisors of gcd D E together with those of D / gcd D E are disjoint from the prime divisors of E / gcd D E. This is an unconditional elementary lemma.
-- source:
--   GPY monomial joint (GPYMonomialJoint.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_primeFactors_gcd_disjoint_right {D E : ℕ} (hsqD : Squarefree D)
    (hsqE : Squarefree E) :
    Disjoint ((Nat.gcd D E).primeFactors ∪ (D / Nat.gcd D E).primeFactors)
      (E / Nat.gcd D E).primeFactors := by sorry
