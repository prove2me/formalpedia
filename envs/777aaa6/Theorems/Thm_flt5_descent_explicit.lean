-- Prove2me | Theorems.Thm_flt5_descent_explicit
-- name    : flt5_descent_explicit
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T13:39:03.487095+00:00
-- url     : https://prove2.me/theorems/4423d3f7-d9d2-49a5-acea-04d86d30fc39
-- statement:
--   FLT-5 explicit descent via Dirichlet 1825. Given a^5+b^5=c^5 with gcd(a,b)=1, 5|c, c=5*c1, a+b=5^4*w, Phi(a,b)=5*v, w*v=c1^5, gcd(w,v)=1, and the explicit 5th-power representations w=r^5 and v=s^5, produce a strictly smaller primitive solution. Since w*v=(rs)^5=c1^5, we have r*s=c1. The construction of (a',b',c') uses Dirichlet's 1825 argument: factoring in Z[zeta_5] where a+b*zeta_5 = u*(alpha)^5 for a unit u and element alpha, then extracting a',b' from real/imaginary parts. This is the core arithmetic-geometric step requiring unique factorization in Z[zeta_5].

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_descent_explicit (a b c w v c1 r s : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1) (hw : a + b = 5 ^ 4 * w) (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * v) (hwv : w * v = c1 ^ 5) (hcop_wv : Int.gcd w v = 1) (hr : w = r ^ 5) (hs : v = s ^ 5) : ∃ a' b' c' : ℤ, a' ^ 5 + b' ^ 5 = c' ^ 5 ∧ Int.gcd a' b' = 1 ∧ (5 : ℤ) ∣ c' ∧ c' ≠ 0 ∧ c'.natAbs < c.natAbs := by sorry
