-- Prove2me | Theorems.Thm_flt5_5dvd_phi5_of_5dvd_sum
-- name    : flt5_5dvd_phi5_of_5dvd_sum
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T07:13:56.838546+00:00
-- url     : https://prove2.me/theorems/8a4720f5-be8b-477d-bc12-d811cfcd4386
-- statement:
--   If 5|(a+b) then 5|Phi5(a,b). Proof: in ZMod 5, b≡-a so Phi5(a,b)≡Phi5(a,-a)=5a^4≡0 (mod 5). Uses decide on ZMod 5.

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem flt5_5dvd_phi5_of_5dvd_sum (a b : ℤ) (h5ab : (5 : ℤ) ∣ a + b) : (5 : ℤ) ∣ a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 := by sorry
