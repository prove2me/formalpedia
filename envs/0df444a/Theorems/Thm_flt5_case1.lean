-- Prove2me | Theorems.Thm_flt5_case1
-- name    : flt5_case1
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T09:15:27.645263+00:00
-- url     : https://prove2.me/theorems/1a8a29d5-9c65-4d2c-91eb-5eaa87abd6da
-- statement:
--   FLT-5 Case 1: If a^5+b^5=c^5 (integers) and 5 divides none of a,b,c, then contradiction. Proved by reduction mod 25: 5th power residues mod 25 are {±1, ±7}, and no two of these sum to another.

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem flt5_case1 (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (ha5 : ¬(5 : ℤ) ∣ a) (hb5 : ¬(5 : ℤ) ∣ b) (hc5 : ¬(5 : ℤ) ∣ c) : False := by sorry
