-- Prove2me | Theorems.Thm_flt7_residue_constraint
-- name    : flt7_residue_constraint
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T09:51:41.736205+00:00
-- url     : https://prove2.me/theorems/0def5e5e-1a5d-4e0c-bf52-d9de83d1ce62
-- statement:
--   For any integers a, b, c satisfying a^7+b^7=c^7, we have 7 | a+b-c. Proof: by Fermat's Little Theorem (7 | a^7-a, 7 | b^7-b, 7 | c^7-c), adding the first two and subtracting the third gives 7 | (a^7+b^7-c^7)-(a+b-c) = 0-(a+b-c). This is a key congruence for FLT-7: any hypothetical solution must satisfy a+b ≡ c (mod 7). In particular, if 7 does not divide a or b, then 7 must divide a+b-c.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.GCD.Basic

theorem flt7_residue_constraint (a b c : ℤ) (h_eq : a^7+b^7 = c^7) : (7:ℤ) ∣ a+b-c := by sorry
