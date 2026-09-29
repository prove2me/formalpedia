-- Prove2me | Theorems.Thm_Martingale_norm_exp_div_one_add_sub_gaussian_le
-- name    : Martingale.norm_exp_div_one_add_sub_gaussian_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T19:21:12.18953+00:00
-- url     : https://prove2.me/theorems/6414d05f-71f5-491b-ba92-613ec548d154
-- title:
--   Cubic comparison of $e^{ix}/(1+ix)$ with the Gaussian factor $e^{-x^2/2}$
-- statement:
--   For every real $x$ with $|x| \le 1$,
--
--   $$\left\| \frac{e^{ix}}{1 + ix} \;-\; e^{-x^{2}/2} \right\| \;\le\; |x|^{3}.$$
--
--   This is the analytic heart of McLeish's proof of the martingale central limit theorem, and the point at which the Gaussian actually appears.
--
--   **The role it plays.** McLeish factors the characteristic function as
--   $$e^{i\theta S_n} \;=\; J^{(1)}_n \cdot J^{(2)}_n, \qquad J^{(1)}_n = \prod_{k<n}\bigl(1 + i\theta Z_k\bigr), \qquad J^{(2)}_n = \frac{e^{i\theta S_n}}{\prod_{k<n}(1 + i\theta Z_k)} .$$
--   The first factor is handled by the martingale property alone: $\mathbb{E}\,J^{(1)}_n = 1$ exactly. All the analysis is therefore concentrated in $J^{(2)}_n$, which factors termwise as $\prod_{k<n} e^{i\theta Z_k}/(1 + i\theta Z_k)$.
--
--   This lemma says each of those factors agrees with $e^{-\theta^2 Z_k^2/2}$ up to a *cubic* error. Consequently
--   $$\left\| J^{(2)}_n - e^{-\frac{\theta^2}{2}\sum_{k<n} Z_k^2} \right\| \;\le\; \sum_{k<n} \bigl|\theta Z_k\bigr|^{3},$$
--   and the right-hand side vanishes under the standard negligibility hypothesis $\max_{k<n}|Z_k| \to 0$ together with $\sum_{k<n} Z_k^2 \to \sigma^2$, since $\sum_k |Z_k|^3 \le \bigl(\max_k |Z_k|\bigr)\sum_k Z_k^2$. The limiting-variance hypothesis then turns the exponent into $-\theta^2\sigma^2/2$, which is precisely the Gaussian characteristic function.
--
--   **Why the exponent $3$ is the right one.** Both $e^{ix}/(1+ix)$ and $e^{-x^2/2}$ have the expansion $1 - x^2/2 + O(|x|^3)$: the linear terms cancel because $1 + ix$ is the first-order Taylor factor of $e^{ix}$, and the quadratic terms agree because $(1+ix)^{-1} = 1 - ix - x^2 + \dots$ contributes exactly the missing $-x^2/2$. A merely quadratic bound would be useless — $\sum_k Z_k^2$ converges to $\sigma^2 \neq 0$, so a quadratic error would not vanish. It is the cancellation through second order that makes the whole argument work.
--
--   **Proof sketch.** Since $|1 + ix| = \sqrt{1+x^2} \ge 1$, the denominator can be cleared, reducing the claim to $\bigl\|e^{ix} - (1+ix)e^{-x^2/2}\bigr\| \le |x|^3$. Writing $T = 1 + ix - x^2/2 - ix^3/6$ for the third-order Taylor polynomial of $e^{ix}$, the difference splits into three pieces: the Taylor remainder $\|e^{ix} - T\| \le \tfrac{5}{96}|x|^4$; the exact algebraic identity $T - (1+ix)(1 - x^2/2) = ix^3/3$, of modulus $|x|^3/3$; and $\|1+ix\|\cdot\bigl|(1 - x^2/2) - e^{-x^2/2}\bigr| \le 2\cdot x^4/4$. For $|x| \le 1$ these sum to at most $\bigl(\tfrac{5}{96} + \tfrac13 + \tfrac12\bigr)|x|^3 < |x|^3$.
--
--   The hypothesis $|x| \le 1$ is what the negligibility of the martingale increments supplies in the application; no cubic bound of this form can hold globally, since the left-hand side is bounded while $|x|^3$ is not — the inequality is genuinely a small-$x$ statement, which is exactly the regime the triangular-array setup produces.
-- source:
--   B. M. Brown, "Martingale Central Limit Theorems", Annals of Mathematical Statistics 42 (1971) 59-66, Theorem 2; D. L. McLeish, "Dependent Central Limit Theorems and Invariance Principles", Annals of Probability 2 (1974) 620-628, Theorem 2.3; P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press 1980, Theorem 3.2.

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exponential

theorem Martingale.norm_exp_div_one_add_sub_gaussian_le (x : ℝ) (hx : |x| ≤ 1) :
    ‖Complex.exp (Complex.I * x) / (1 + Complex.I * (x : ℂ))
        - ((Real.exp (-(x ^ 2) / 2) : ℝ) : ℂ)‖ ≤ |x| ^ 3 := by sorry
