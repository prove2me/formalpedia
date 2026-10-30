-- Prove2me | Theorems.Thm_gpy_prime_dvd_lcm
-- name    : gpy_prime_dvd_lcm
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T02:36:03.435987+00:00
-- url     : https://prove2.me/theorems/4db49d1f-81a9-4ce3-beab-ad2b37f03869
-- title:
--   A prime dividing a lcm divides one of the factors
-- statement:
--   If a prime p divides Nat.lcm m n, then p divides m or p divides n. Formalization Note: the statement uses only Mathlib terms.
-- source:
--   GPY good-count local evaluation, formalized from Mathlib (prime factorization of the good-pair condition)

import Mathlib
open Classical

theorem gpy_prime_dvd_lcm {p m n : ℕ} (hp : Nat.Prime p) (h : p ∣ Nat.lcm m n) :
    p ∣ m ∨ p ∣ n := by sorry
