-- Prove2me | Theorems.Thm_gpy_coprime_div_of_squarefree
-- name    : gpy_coprime_div_of_squarefree
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T23:11:16.685174+00:00
-- url     : https://prove2.me/theorems/1ba01b58-0b48-407a-9eb8-a2ac2c62fb76
-- title:
--   Complementary quotient of a divisor of a squarefree number is coprime to it
-- statement:
--   For a squarefree natural number n and a divisor d of n, the quotient n / d is coprime to d. This is an unconditional elementary lemma.
-- source:
--   GPY monomial joint (GPYMonomialJoint.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_coprime_div_of_squarefree {n d : ℕ} (hsq : Squarefree n)
    (hd : d ∣ n) : Nat.Coprime (n / d) d := by sorry
