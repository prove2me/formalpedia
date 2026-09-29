-- Prove2me | Theorems.Thm_flt5_5dvd_c5_of_5dvd_c
-- name    : flt5_5dvd_c5_of_5dvd_c
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T07:18:50.277173+00:00
-- url     : https://prove2.me/theorems/4d2fcc48-a9f4-4504-ac40-8afe67918d92
-- statement:
--   If 5|c then 5|c^5. Immediate from dvd_pow.

import Mathlib.Data.Int.Basic

theorem flt5_5dvd_c5_of_5dvd_c (c : ℤ) (h5c : (5 : ℤ) ∣ c) : (5 : ℤ) ∣ c ^ 5 := by sorry
