-- Prove2me | Theorems.Thm_flt7_gcd_apb_phi7_dvd_7
-- name    : flt7_gcd_apb_phi7_dvd_7
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T08:51:17.201066+00:00
-- url     : https://prove2.me/theorems/1556bc1e-7e17-407c-ad15-c3a9299a9ca4
-- statement:
--   For coprime positive natural numbers a, b: the gcd of (a+b) and the natural number quotient (a^7+b^7)/(a+b) divides 7. This is the key upper bound on the gcd in the FLT-7 Kummer descent. Combined with the lower bound (7 | gcd when 7 | a+b), it shows gcd = 1 or 7, which is central to proving 7^6 || (a+b) in the descent argument.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.Nat.GCD.Basic

theorem flt7_gcd_apb_phi7_dvd_7 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hgcd : Nat.Coprime a b) : Nat.gcd (a+b) ((a^7+b^7)/(a+b)) ∣ 7 := by sorry
