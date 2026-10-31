-- Prove2me | Theorems.Thm_gpy_modEq_of_prime_dvd_natAbs_diff
-- name    : gpy_modEq_of_prime_dvd_natAbs_diff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T22:22:57.544989+00:00
-- url     : https://prove2.me/theorems/37789469-731f-4ffd-b827-a060d29ab51f
-- title:
--   Divisibility of the absolute difference gives congruence mod p
-- statement:
--   Conversely, if a prime p divides the absolute value of the integer difference a - b, then a is congruent to b modulo p, proved by cases on the order of a and b. Pure Mathlib statement.
-- source:
--   GPY defect control: exact characterizations and exact sum identities for the compatible-but-not-good (defect) pairs

import Mathlib
open Classical

theorem gpy_modEq_of_prime_dvd_natAbs_diff {p : ℕ} (_hp : Nat.Prime p)
    {a b : ℕ} (hdvd : p ∣ Int.natAbs ((a : ℤ) - (b : ℤ))) :
    a ≡ b [MOD p] := by sorry
