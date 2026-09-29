-- Prove2me | Theorems.Thm_flt5_z_zeta5_core
-- name    : flt5_z_zeta5_core
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T13:51:11.426+00:00
-- url     : https://prove2.me/theorems/76eec253-dec9-447e-9844-3f88b9db4164
-- statement:
--   FLT-5 core descent via Z[zeta_5] (Dirichlet 1825). Given a^5+b^5=c^5 with gcd(a,b)=1, 5|c=5*c1, a+b=5^4*r^5, Phi(a,b)=5*s^5, gcd(r,s)=1, and r*s=c1, produce a strictly smaller primitive solution. This is the algebraic core of Dirichlet's 1825 descent: in Z[zeta_5] (the ring of integers of Q(zeta_5), which is a PID with class number 1), the element a + b*zeta_5 factors as a unit times a 5th power, and extracting the components via the norm map gives the new smaller triple. The key steps are: (1) Z[zeta_5] is a PID; (2) gcd(a+b*zeta_5^k, a+b*zeta_5^j) divides 5*(1-zeta_5) for k≠j; (3) unique factorization gives a+b*zeta_5 = u*alpha^5; (4) taking norms and real parts extracts a',b' with c'.natAbs = |r*s| = |c1| < |5*c1| = |c|.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_z_zeta5_core (a b c r s c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1) (hw : a + b = 5 ^ 4 * r ^ 5) (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5) (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1) : ∃ a' b' c' : ℤ, a' ^ 5 + b' ^ 5 = c' ^ 5 ∧ Int.gcd a' b' = 1 ∧ (5 : ℤ) ∣ c' ∧ c' ≠ 0 ∧ c'.natAbs < c.natAbs := by sorry
