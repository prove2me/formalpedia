-- Prove2me | Theorems.Thm_Real_log_le_sub_inv_div_two
-- name    : Real.log_le_sub_inv_div_two
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-05T18:31:48.636667+00:00
-- url     : https://prove2.me/theorems/f8a7cb1b-e490-4fa5-9c44-1c34082810ef
-- title:
--   Sharp upper bound $\log t \le \tfrac12\left(t - \tfrac1t\right)$ for $t \ge 1$
-- statement:
--   For every real $t \ge 1$,
--   $$\log t \;\le\; \frac{1}{2}\left(t - \frac{1}{t}\right).$$
--
--   The right-hand side is the average of Mathlib's two first-order bounds $\log t \le t - 1$ and $\log t \ge 1 - 1/t$, and unlike either of them it is second-order accurate at $t = 1$; it is exactly the statement $x \le \sinh x$ for $x \ge 0$.
--
--   **Proof.** Put $x = \log t \ge 0$. Then $\sinh x = \tfrac12(e^x - e^{-x}) = \tfrac12\bigl(t - t^{-1}\bigr)$, and $x \le \sinh x$ for $x \ge 0$.
-- source:
--   Standard sharp elementary bounds on the natural logarithm; both are absent from Mathlib. The lower bound is the diagonal Pade approximant of order (1,1) (equivalently 2 artanh((t-1)/(t+1)) >= 2 tanh of half the logarithm), the upper bound is x <= sinh x at x = log t. See e.g. Mitrinovic, Analytic Inequalities (Springer 1970), Chapter III.

import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem Real.log_le_sub_inv_div_two {t : ℝ} (ht : 1 ≤ t) :
    Real.log t ≤ (t - 1 / t) / 2 := by
  sorry
