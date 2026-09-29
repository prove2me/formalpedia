-- Prove2me | Theorems.Thm_flt5_case2
-- name    : flt5_case2
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-05-12T09:46:03.525866+00:00
-- url     : https://prove2.me/theorems/ecaf01dc-dc2b-4194-8c3c-0725016f6f4d
-- statement:
--   FLT-5 Case 2: If a^5+b^5=c^5 (integers), gcd(a,b)=1, and 5 divides c, then contradiction. This is the harder case of FLT-5, proved by Dirichlet (1825) using infinite descent: from 5|c one shows 5^4|(a+b), and the coprime factor structure forces a smaller FLT-5 solution, contradicting well-ordering.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_case2 (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) : False := by sorry
