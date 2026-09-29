-- Prove2me | Theorems.Thm_fltp_residue_constraint
-- name    : fltp_residue_constraint
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T10:02:14.436972+00:00
-- url     : https://prove2.me/theorems/306db9c6-b904-4a84-97b4-c9f6f3db6e27
-- statement:
--   For any prime p and integers a, b, c satisfying a^p+b^p=c^p, p divides a+b-c. This is the general version of flt7_residue_constraint. Proof: Fermat's Little Theorem gives p | a^p-a, p | b^p-b, p | c^p-c; adding the first two and subtracting the third gives p | (a^p+b^p-c^p)-(a+b-c) = 0-(a+b-c), so p | a+b-c.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.GCD.Basic

theorem fltp_residue_constraint (p : ℕ) [hp : Fact (Nat.Prime p)] (a b c : ℤ) (h_eq : a^p+b^p = c^p) : (p:ℤ) ∣ a+b-c := by sorry
