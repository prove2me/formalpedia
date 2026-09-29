-- Prove2me | Theorems.Thm_apb_dvd_pow_add_pow
-- name    : apb_dvd_pow_add_pow
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T10:08:38.654113+00:00
-- url     : https://prove2.me/theorems/799a449d-98a9-4cb5-b9b5-c1944baa0d6c
-- statement:
--   For any odd natural number n and natural numbers a, b, (a+b) divides (a^n+b^n). Proof: lift to ℤ, use sub_dvd_pow_sub_pow to get (a - (-b)) | (a^n - (-b)^n), then apply Odd.neg_pow to convert (-b)^n = -(b^n) and simplify to (a+b) | (a^n+b^n) in ℤ, then cast back to ℕ.

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.GCD.Basic

theorem apb_dvd_pow_add_pow (n : ℕ) (h_odd : Odd n) (a b : ℕ) : (a+b) ∣ (a^n+b^n) := by sorry
