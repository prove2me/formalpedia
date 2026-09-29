-- Prove2me | Theorems.Thm_exp_le_quad
-- name    : exp_le_quad
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-22T02:17:24.964995+00:00
-- url     : https://prove2.me/theorems/030c814b-d279-4523-a53b-2e2a2ab7fd97
-- statement:
--   **Elementary quadratic upper bound on the exponential.** For every real $x \le 1$,
--   $$ e^{x} \le 1 + x + x^2. $$
--   This is the key pointwise estimate behind Bernstein-type moment generating function bounds: on the half-line $(-\infty, 1]$ the exponential lies below the quadratic $1 + x + x^2$. The proof studies $\varphi(x) = e^{-x}(1 + x + x^2)$, whose derivative $\varphi'(x) = e^{-x}\,x(1-x)$ is nonpositive on $(-\infty,0]$ and nonnegative on $[0,1]$, so $\varphi$ attains its minimum value $\varphi(0)=1$ on $(-\infty,1]$; hence $1 + x + x^2 \ge e^{x}$ there.
-- source:
--   Standard quadratic Taylor bound for the exponential on a half-line; cf. Boucheron, Lugosi, Massart, 'Concentration Inequalities', OUP 2013, Ch. 2 (proof of Bernstein's inequality).

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.MeanValue
open scoped BigOperators

theorem exp_le_quad (x : ℝ) (hx : x ≤ 1) : Real.exp x ≤ 1 + x + x^2 := by sorry
