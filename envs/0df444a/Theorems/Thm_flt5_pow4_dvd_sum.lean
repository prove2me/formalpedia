-- Prove2me | Theorems.Thm_flt5_pow4_dvd_sum
-- name    : flt5_pow4_dvd_sum
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T11:16:16.026088+00:00
-- url     : https://prove2.me/theorems/c3019e5e-cb28-4120-ac81-6a614b378584
-- statement:
--   **FLT-5 valuation bound.** If $a^5 + b^5 = c^5$ (integers), $\gcd(a,b)=1$, $5\mid c$, and $c\ne 0$, then $5^4 \mid a+b$.
--
--   Proof: By Fermat's little theorem $5\mid a+b$. Since $\gcd(a,b)=1$ and $5\mid c$, we have $5\nmid a$. By the Lifting the Exponent Lemma (odd prime $p=5$, $p\mid a+b$, $p\nmid a$, $n=5$ odd): $v_5(a^5+b^5) = v_5(a+b)+1$. Also $v_5(c^5) = 5v_5(c)$. Since $c\ne 0$ and $5\mid c$, $v_5(c)\ge 1$, so $v_5(a+b) = 5v_5(c)-1\ge 4$. Hence $5^4\mid a+b$.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.NumberTheory.Multiplicity

theorem flt5_pow4_dvd_sum (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) : (5 : ℤ) ^ 4 ∣ a + b := by sorry
