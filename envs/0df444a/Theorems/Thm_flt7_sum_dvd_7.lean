-- Prove2me | Theorems.Thm_flt7_sum_dvd_7
-- name    : flt7_sum_dvd_7
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T07:40:58.16085+00:00
-- url     : https://prove2.me/theorems/5680d2d8-c77a-4583-8649-fc7aad1e581f
-- statement:
--   If a^7 + b^7 = c^7 for integers a, b, c and 7 divides c, then 7 divides a+b. Proof uses Fermat's little theorem: in ZMod 7, x^7 = x for all x, so a+b ≡ a^7+b^7 = c^7 ≡ c ≡ 0 (mod 7).
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem flt7_sum_dvd_7 (a b c : ℤ) (h_eq : a ^ 7 + b ^ 7 = c ^ 7) (h7c : (7 : ℤ) ∣ c) : (7 : ℤ) ∣ a + b := by sorry
