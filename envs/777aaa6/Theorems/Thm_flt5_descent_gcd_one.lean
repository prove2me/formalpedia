-- Prove2me | Theorems.Thm_flt5_descent_gcd_one
-- name    : flt5_descent_gcd_one
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T06:45:52.620715+00:00
-- url     : https://prove2.me/theorems/210d3a08-9b2e-431e-b53c-968ac84d757e
-- statement:
--   **Descent Case 1 for Dirichlet's FLT-5 proof.** If a^5 + b^5 = c^5, gcd(a,b) = 1, and 5 ∤ c, then gcd(a+b, Φ₅(a,b)) = 1. Proof: By gcd_cyclotomic_dvd_5, D = gcd(a+b,Φ₅) divides 5, so D ∈ {1,5}. If D = 5, then 5|(a+b), hence 5|c^5 = (a+b)·Φ₅, so by Euclid's lemma 5|c, contradicting 5 ∤ c. Therefore D = 1. This coprimality is the key to the first descent case: a+b and Φ₅ must each be 5th powers (by unique factorization in ℤ).

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

theorem flt5_descent_gcd_one (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h_not5c : ¬(5 : ℤ) ∣ c) : Int.gcd (a + b) (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) = 1 := by sorry
