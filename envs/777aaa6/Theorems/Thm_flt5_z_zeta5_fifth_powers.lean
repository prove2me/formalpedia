-- Prove2me | Theorems.Thm_flt5_z_zeta5_fifth_powers
-- name    : flt5_z_zeta5_fifth_powers
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-12T14:03:57.736326+00:00
-- url     : https://prove2.me/theorems/bccc6fb3-a0a3-4b90-bf7b-9c0bea34657b
-- statement:
--   FLT-5 via Z[zeta_5]: from a^5+b^5=(5c1)^5, gcd(a,b)=1, a+b=5^4*r^5, Phi(a,b)=5*s^5, gcd(r,s)=1, r*s=c1, produce coprime p,q with p^5+q^5=c1^5. In Z[zeta_5], (a+b*zeta_5^k) for k=0..4 factor a^5+b^5. Since Z[zeta_5] is a PID and these factors are pairwise coprime (up to (1-zeta_5)), each is a 5th power times a unit. Taking norms over Q(zeta_5)/Q and reading off real parts gives p, q with p^5+q^5=c1^5 and gcd(p,q)=1. This is the core of Dirichlet's 1825 descent.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_z_zeta5_fifth_powers (a b c r s c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1) (hw : a + b = 5 ^ 4 * r ^ 5) (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5) (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1) : ∃ p q : ℤ, p ^ 5 + q ^ 5 = c1 ^ 5 ∧ Int.gcd p q = 1 := by sorry
