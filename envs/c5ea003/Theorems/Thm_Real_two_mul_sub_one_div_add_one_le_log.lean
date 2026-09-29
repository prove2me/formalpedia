-- Prove2me | Theorems.Thm_Real_two_mul_sub_one_div_add_one_le_log
-- name    : Real.two_mul_sub_one_div_add_one_le_log
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-05T18:30:57.104922+00:00
-- url     : https://prove2.me/theorems/3d551cb9-314c-40db-8d30-94d522bd428c
-- title:
--   Sharp lower bound $\frac{2(t-1)}{t+1} \le \log t$ for $t \ge 1$
-- statement:
--   For every real $t \ge 1$,
--   $$\frac{2(t-1)}{t+1} \;\le\; \log t .$$
--
--   This is the $(1,1)$ Pade lower bound for the logarithm. It is second-order accurate at $t = 1$ -- writing $t = e^{2u}$ it says exactly $\tanh u \le u$ -- and is therefore strictly sharper than Mathlib's `Real.one_sub_inv_le_log_of_pos` ($1 - 1/t \le \log t$), which is only first-order accurate. Sharpness at this order is what makes it usable as the *lower* half of a second-order estimate of a relative entropy.
--
--   **Proof.** The function $g(t) = \log t - 2 + \frac{4}{t+1}$ (note $2 - \frac{4}{t+1} = \frac{2(t-1)}{t+1}$) satisfies $g(1) = 0$ and
--   $$g'(t) \;=\; \frac1t - \frac{4}{(t+1)^2} \;=\; \frac{(t-1)^2}{t\,(t+1)^2} \;\ge\; 0 \qquad (t > 0),$$
--   so $g$ is monotone on $[1,\infty)$ and hence $g(t) \ge g(1) = 0$ there.
-- source:
--   Standard sharp elementary bounds on the natural logarithm; both are absent from Mathlib. The lower bound is the diagonal Pade approximant of order (1,1) (equivalently 2 artanh((t-1)/(t+1)) >= 2 tanh of half the logarithm), the upper bound is x <= sinh x at x = log t. See e.g. Mitrinovic, Analytic Inequalities (Springer 1970), Chapter III.

import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem Real.two_mul_sub_one_div_add_one_le_log {t : ℝ} (ht : 1 ≤ t) :
    2 * (t - 1) / (t + 1) ≤ Real.log t := by
  sorry
