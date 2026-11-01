-- Prove2me | Theorems.Thm_gpy_sq_not_dvd_both
-- name    : gpy_sq_not_dvd_both
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T22:55:42.208912+00:00
-- url     : https://prove2.me/theorems/bab7c599-a298-4823-be56-01cb04771d5d
-- title:
--   A prime cannot divide both parts of a squarefree number
-- statement:
--   For a squarefree natural number n and a divisor d of n, no prime p divides both d and the complementary quotient n / d: that would give p * p dividing n. This is an unconditional elementary lemma.
-- source:
--   GPY monomial joint (GPYMonomialJoint.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_sq_not_dvd_both {n d : ℕ} (hsq : Squarefree n) (hd : d ∣ n)
    {p : ℕ} (hp : p.Prime) : ¬ (p ∣ d ∧ p ∣ n / d) := by sorry
