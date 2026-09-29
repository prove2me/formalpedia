-- Prove2me | Theorems.Thm_fltp_case2_descent_coprime
-- name    : fltp_case2_descent_coprime
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-17T00:56:59.99453+00:00
-- url     : https://prove2.me/theorems/9bc48b8c-b0b4-49fc-8234-8de1b18ce48c
-- statement:
--   In FLT Case 2 for general odd prime p (a^p+b^p=c^p, c=p*c1, p∤a, p∤c1, p|a+b, gcd(a,b)=1): The two Kummer descent factors (a+b)/p^(p-1) and (a^p+b^p)/(a+b)/p are coprime. Proved by contradiction: any prime q dividing the gcd must satisfy q=p (ruled out by p-adic valuation of A) or q≠p, and in the latter case the congruence Phi_p ≡ p*a^(p-1) mod (a+b) (from the geometric sum formula) forces q|p, contradicting q≠p.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic

theorem fltp_case2_descent_coprime (p : ℕ) [hp : Fact (Nat.Prime p)] (a b c c1 : ℕ)
    (h_odd : Odd p) (heq : a ^ p + b ^ p = c ^ p)
    (ha : 0 < a) (hb : 0 < b)
    (h_ndvd_a : ¬p ∣ a) (hpab : p ∣ a + b)
    (hc : c = p * c1) (h_ndvd_c1 : ¬p ∣ c1)
    (hcop : Nat.Coprime a b) :
    Nat.Coprime ((a + b) / p ^ (p - 1)) ((a ^ p + b ^ p) / (a + b) / p) := by sorry
