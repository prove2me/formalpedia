-- Prove2me | Theorems.Thm_gpy_prime_dvd_natAbs_diff_of_modEq
-- name    : gpy_prime_dvd_natAbs_diff_of_modEq
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T21:50:18.688889+00:00
-- url     : https://prove2.me/theorems/a346523d-00db-45de-a544-5ba6175f4ed7
-- title:
--   Congruence mod p gives divisibility of the absolute difference
-- statement:
--   A congruence a congruent to b modulo a prime p implies p divides the absolute value of the integer difference a - b, proved by cases on the order of a and b. Pure Mathlib statement.
-- source:
--   GPY defect control: exact characterizations and exact sum identities for the compatible-but-not-good (defect) pairs

import Mathlib
open Classical

theorem gpy_prime_dvd_natAbs_diff_of_modEq {p : ℕ} (_hp : Nat.Prime p)
    {a b : ℕ} (hcong : a ≡ b [MOD p]) :
    p ∣ Int.natAbs ((a : ℤ) - (b : ℤ)) := by sorry
