-- Prove2me | Theorems.Thm_gpy_prime_dvd_finset_lcm
-- name    : gpy_prime_dvd_finset_lcm
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T02:38:06.992659+00:00
-- url     : https://prove2.me/theorems/697f9149-4ce4-4f50-842d-c0bab82c5dc5
-- title:
--   A prime dividing a finset lcm divides some member
-- statement:
--   If a prime p divides the lcm of a finset-indexed family of natural numbers, then p divides some member of the family. Formalization Note: the statement uses only Mathlib terms.
-- source:
--   GPY good-count local evaluation, formalized from Mathlib (prime factorization of the good-pair condition)

import Mathlib
open Classical

theorem gpy_prime_dvd_finset_lcm {ι : Type*} {s : Finset ι} {f : ι → ℕ} {p : ℕ}
    (hp : Nat.Prime p) (h : p ∣ s.lcm f) : ∃ j ∈ s, p ∣ f j := by sorry
