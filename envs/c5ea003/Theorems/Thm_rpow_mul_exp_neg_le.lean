-- Prove2me | Theorems.Thm_rpow_mul_exp_neg_le
-- name    : rpow_mul_exp_neg_le
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-22T02:22:38.948547+00:00
-- url     : https://prove2.me/theorems/13faeeb7-e862-40d1-a98e-878e1f4fab39
-- statement:
--   **Maximum of $x^q e^{-\lambda x}$.** For real exponent $q>0$, rate $\lambda>0$, and $x\ge 0$,
--   $$ x^{q}\, e^{-\lambda x} \le \Big(\tfrac{q}{\lambda e}\Big)^{q}. $$
--   The right-hand side is the global maximum of $x \mapsto x^q e^{-\lambda x}$ on $[0,\infty)$, attained at $x = q/\lambda$. This is the elementary inequality that turns a moment generating function bound into a moment (or tail) bound via the Cramér–Chernoff method: $\mathbb E|Z|^q \le (q/(\lambda e))^q\,\mathbb E[e^{\lambda|Z|}]$. The proof takes logarithms and reduces to the standard inequality $\log u \le u-1$ applied at $u = \lambda x/q$.
-- source:
--   Standard Cramér–Chernoff moment/tail device; Boucheron–Lugosi–Massart, Concentration Inequalities, OUP 2013, Ch. 2.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
open scoped BigOperators

theorem rpow_mul_exp_neg_le (q lam x : ℝ) (hq : 0 < q) (hlam : 0 < lam) (hx : 0 ≤ x) :
    x ^ q * Real.exp (-(lam * x)) ≤ (q / (lam * Real.exp 1)) ^ q := by sorry
