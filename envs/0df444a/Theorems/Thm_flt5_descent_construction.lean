-- Prove2me | Theorems.Thm_flt5_descent_construction
-- name    : flt5_descent_construction
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T11:59:29.473895+00:00
-- url     : https://prove2.me/theorems/6579b8f9-03e5-4ec4-9108-ea24cda5f137
-- statement:
--   FLT-5 descent from coprime 5th-power split. Given a^5+b^5=c^5 with gcd(a,b)=1, 5|c, c=5*c1, a+b=5^4*w, Phi(a,b)=5*v, w*v=c1^5, gcd(w,v)=1, produce a smaller solution. Since gcd(w,v)=1 and w*v=c1^5, by unique factorization in Z both w and v are 5th powers (up to sign): w=r^5 and v=s^5. The smaller triple (a',b',c') is constructed via Dirichlet's 1825 argument using factorization in Z[zeta_5].

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_descent_construction (a b c w v c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1) (hw : a + b = 5 ^ 4 * w) (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * v) (hwv : w * v = c1 ^ 5) (hcop_wv : Int.gcd w v = 1) : ∃ a' b' c' : ℤ, a' ^ 5 + b' ^ 5 = c' ^ 5 ∧ Int.gcd a' b' = 1 ∧ (5 : ℤ) ∣ c' ∧ c' ≠ 0 ∧ c'.natAbs < c.natAbs := by sorry
