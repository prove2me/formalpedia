-- Prove2me | Theorems.Thm_gpy_exists_modEq_prime_finset
-- name    : gpy_exists_modEq_prime_finset
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T02:43:17.445483+00:00
-- url     : https://prove2.me/theorems/36eebafd-b48d-4187-9101-45877b9a5444
-- title:
--   Simultaneous congruences modulo distinct primes
-- statement:
--   For any residue function a and any finset P of primes, there is a w with w congruent to a q modulo q for every q in P: the Chinese remainder theorem over a finset of primes. Formalization Note: the statement uses only Mathlib terms.
-- source:
--   GPY good-count local evaluation, formalized from Mathlib (prime factorization of the good-pair condition)

import Mathlib
open Classical

theorem gpy_exists_modEq_prime_finset {P : Finset ℕ} (a : ℕ → ℕ)
    (hP : ∀ q ∈ P, Nat.Prime q) :
    ∃ w, ∀ q ∈ P, w ≡ a q [MOD q] := by sorry
