-- Prove2me | Theorems.Thm_fltp_case2_descent_eq
-- name    : fltp_case2_descent_eq
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-17T00:56:50.123479+00:00
-- url     : https://prove2.me/theorems/92759710-e299-4dd0-94f8-e9e87dec1c47
-- statement:
--   In FLT Case 2 for general odd prime p (p | c, p ∤ a, p ∤ c1, p | a+b, c = p*c1, a^p + b^p = c^p): The Kummer descent equation holds: ((a+b)/p^(p-1)) * ((a^p+b^p)/(a+b)/p) = c1^p. This is proved by cancelling p^p from both sides using LTE and divisibility properties of the p-adic valuation.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity

theorem fltp_case2_descent_eq (p : ℕ) [hp : Fact (Nat.Prime p)] (a b c c1 : ℕ)
    (h_odd : Odd p) (heq : a ^ p + b ^ p = c ^ p)
    (ha : 0 < a) (hb : 0 < b)
    (h_ndvd_a : ¬p ∣ a) (hpab : p ∣ a + b)
    (hc : c = p * c1) (h_ndvd_c1 : ¬p ∣ c1) :
    (a + b) / p ^ (p - 1) * ((a ^ p + b ^ p) / (a + b) / p) = c1 ^ p := by sorry
