-- Prove2me | Theorems.Thm_gpy_coprime_prime_prod
-- name    : gpy_coprime_prime_prod
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T02:40:17.10038+00:00
-- url     : https://prove2.me/theorems/8b6afa88-52ec-4fab-be62-ec01a41c85df
-- title:
--   A prime outside a finset of primes is coprime to its product
-- statement:
--   A prime p is coprime to the product of a finset of primes none of which equals p. Formalization Note: the statement uses only Mathlib terms.
-- source:
--   GPY good-count local evaluation, formalized from Mathlib (prime factorization of the good-pair condition)

import Mathlib
open Classical

theorem gpy_coprime_prime_prod {P : Finset ℕ} {p : ℕ} (hp : Nat.Prime p)
    (hP : ∀ q ∈ P, Nat.Prime q) (hne : ∀ q ∈ P, q ≠ p) :
    Nat.Coprime p (∏ q ∈ P, q) := by sorry
