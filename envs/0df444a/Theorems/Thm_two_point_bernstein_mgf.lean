-- Prove2me | Theorems.Thm_two_point_bernstein_mgf
-- name    : two_point_bernstein_mgf
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-22T02:17:31.324712+00:00
-- url     : https://prove2.me/theorems/ff25cd10-9964-4c55-b494-1e11755e600a
-- statement:
--   **Two-point Bernstein MGF inequality (variance form).** Let $X$ be a centered two-point random variable taking value $a$ with probability $p \in [0,1]$ and value $b$ with probability $1-p$, with $p a + (1-p) b = 0$. If both values satisfy $a \le 1$ and $b \le 1$, then the moment generating function is controlled by the exponential of the variance $V = p a^2 + (1-p) b^2$:
--   $$ p\, e^{a} + (1-p)\, e^{b} \le \exp\!\big( p a^2 + (1-p) b^2 \big). $$
--   Unlike the Hoeffding (range-based) bound, the exponent here is the *exact variance*, which is the sharp scaling needed for Bernstein concentration. The proof applies the quadratic bound $e^{a} \le 1 + a + a^2$ and $e^{b} \le 1 + b + b^2$ (valid since $a, b \le 1$), takes the convex combination, uses centering $p a + (1-p) b = 0$ to kill the linear term, and finishes with $1 + V \le e^{V}$.
-- source:
--   Bernstein's inequality, MGF/variance form; Boucheron, Lugosi, Massart, 'Concentration Inequalities', OUP 2013, Ch. 2; Bernstein 1924.

import Mathlib.Analysis.SpecialFunctions.Exp
open scoped BigOperators

theorem two_point_bernstein_mgf (p a b : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcent : p * a + (1 - p) * b = 0) (ha : a ≤ 1) (hb : b ≤ 1) :
    p * Real.exp a + (1 - p) * Real.exp b ≤
      Real.exp (p * a^2 + (1 - p) * b^2) := by sorry
