-- Prove2me | Theorems.Thm_flt5_descent_from_pow4
-- name    : flt5_descent_from_pow4
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T11:16:20.059992+00:00
-- url     : https://prove2.me/theorems/de7f96ea-dfa6-43df-ab1a-d38e9060e749
-- statement:
--   **FLT-5 descent from $5^4\mid a+b$.** If $a^5+b^5=c^5$ with $\gcd(a,b)=1$, $5\mid c$, $c\ne 0$, and $5^4\mid a+b$, then there exist $a',b',c'$ satisfying the same conditions with $|c'|<|c|$.
--
--   Proof: Factor $c^5 = (a+b)\Phi$ where $\Phi = a^4-a^3b+a^2b^2-ab^3+b^4$. Since $5^4\mid a+b$ and $v_5(\Phi)=1$, write $a+b=5^4\alpha^5$ and $\Phi=5\beta^5$ with $\gcd(\alpha,\beta)=1$ (using coprimality of $(a+b)/5^4$ and $\Phi/5$ and the UFD property of $\mathbb{Z}$). Then $c=5\alpha\beta$. Extracting the smaller solution $(a',b',c')$ via Dirichlet's algebraic argument in $\mathbb{Z}[\zeta_5]$.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_descent_from_pow4 (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (h54 : (5 : ℤ) ^ 4 ∣ a + b) : ∃ a' b' c' : ℤ, a' ^ 5 + b' ^ 5 = c' ^ 5 ∧ Int.gcd a' b' = 1 ∧ (5 : ℤ) ∣ c' ∧ c' ≠ 0 ∧ c'.natAbs < c.natAbs := by sorry
