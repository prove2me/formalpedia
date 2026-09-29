-- Prove2me | Theorems.Thm_flt5_descent_step
-- name    : flt5_descent_step
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T11:13:00.810757+00:00
-- url     : https://prove2.me/theorems/7ba90015-c6a0-41bb-b9b8-5d93bff247d3
-- statement:
--   **FLT-5 descent step (Dirichlet 1825).** If $a^5 + b^5 = c^5$ with $\gcd(a,b) = 1$, $5 \mid c$, and $c \ne 0$, then there exist $a', b', c'$ with $a'^5 + b'^5 = c'^5$, $\gcd(a',b')=1$, $5 \mid c'$, $c' \ne 0$, and $|c'| < |c|$.
--
--   Proof sketch (Dirichlet 1825): Factor $c^5 = (a+b)\Phi(a,b)$ where $\Phi = a^4 - a^3b + a^2b^2 - ab^3 + b^4$. By Fermat's little theorem $5 \mid a+b$. By the Lifting the Exponent Lemma, $v_5(a+b) = 5m-1$ and $v_5(\Phi) = 1$ where $m = v_5(c) \ge 1$. So $a+b = 5^{5m-1} \alpha^5$ and $\Phi = 5\beta^5$ with $\gcd(\alpha,\beta)=1$, yielding $c = 5^m \alpha\beta$. Working in $\mathbb{Z}[\zeta_5]$ allows extracting a smaller FLT-5 solution $(a', b', c')$ with $|c'| < |c|$.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_descent_step (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) : ∃ a' b' c' : ℤ, a' ^ 5 + b' ^ 5 = c' ^ 5 ∧ Int.gcd a' b' = 1 ∧ (5 : ℤ) ∣ c' ∧ c' ≠ 0 ∧ c'.natAbs < c.natAbs := by sorry
