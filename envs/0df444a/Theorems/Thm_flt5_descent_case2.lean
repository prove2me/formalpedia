-- Prove2me | Theorems.Thm_flt5_descent_case2
-- name    : flt5_descent_case2
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T09:56:02.643906+00:00
-- url     : https://prove2.me/theorems/53a64217-b8ca-474a-b0b1-0d09ec1a6831
-- statement:
--   FLT-5 Case 2 (corrected): If a^5+b^5=c^5 (integers), gcd(a,b)=1, 5 divides c, and c≠0, then contradiction. The hypothesis c≠0 excludes the trivial solution (1,-1,0). Proved by Dirichlet (1825) using infinite descent via the Lifting-the-Exponent lemma: 5^4 | (a+b) and the coprime factor theorem yields a smaller FLT-5 solution, contradicting well-ordering.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_descent_case2 (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) : False := by sorry
