-- Prove2me | Theorems.Thm_YuanDGD_Sublinear_thm2_recursion
-- name    : YuanDGD.Sublinear.thm2_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:20:24.850553+00:00
-- url     : https://prove2.me/theorems/14e15082-8d28-48f1-b7cf-e773fd62fc19
-- title:
--   Proof of Theorem 2, p. 11 — r̄(k + 1) ≤ r̄(k) − (α/(2C²))r̄²(k) + α³D²L_h²/(2(1 − β)²)
-- statement:
--   Under Assumption 1, let $0 < \alpha \le \min\{(1+\lambda_n(W))/L_h,\ 1/L_{\bar f}\}$, let $[\tilde x_{(i)}]$ be a minimizer of the Lyapunov function $\xi_\alpha$ (8), and let $x^* \in \mathcal X^*$. With $C$ the constant (17) built from $[\tilde x_{(i)}]$ and $x^*$, $D$ the constant (10), and $\bar r(k) = \bar f(\bar x(k)) - \bar f(x^*)$, for every $k \ge 0$
--   $$\bar r(k+1) \le \bar r(k) - \frac{\alpha}{2C^2}\,\bar r(k)^2 + \frac{\alpha^3 D^2 L_h^2}{2(1-\beta)^2}.$$
--
--   This recursion in $\bar r$ alone drives the $O(1/(\alpha k))$ rate of Theorem 2: as long as the quadratic decrease dominates the constant error term, $\bar r$ decreases like the iterates of $r \mapsto r - c r^2$.
--
--   **Formalization Note.** $C$ is computed with one fixed $x^* \in \mathcal X^*$ (on the page $x^*$ is $x^*(k)$). A minimizer of $\xi_\alpha$ is a hypothesis (the paper's argument for its existence does not follow from Assumption 1). In the degenerate case $C = 0$, Lean's convention $a/0 = 0$ makes the middle term vanish, and the statement reduces to $\bar r(k+1) \le \bar r(k) + \alpha^3D^2L_h^2/(2(1-\beta)^2)$, which is still true.
-- source:
--   Yuan, Ling & Yin, On the Convergence of Decentralized Gradient Descent, arXiv:1310.7063v3, p. 11, proof of Theorem 2, display after (17)

import Mathlib
import Definitions.Def_YuanDGD_Sublinear_Setting

namespace YuanDGD.Sublinear

open YuanDGD.Linear

/-- Yuan–Ling–Yin, arXiv:1310.7063v3, proof of Theorem 2, p. 11, the display after (17): under
Assumption 1, if `0 < α ≤ min{(1 + λₙ(W))/L_h, 1/L_f̄}`, `[x̃₍ᵢ₎]` minimizes `ξ_α` and `x* ∈ X*`, then
with `C` of (17), `r̄(k + 1) ≤ r̄(k) − (α/(2C²))r̄²(k) + α³D²L_h²/(2(1 − β)²)` for every `k`. -/
theorem thm2_recursion {n p : ℕ} (G : SimpleGraph (Fin n)) (W : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → E p → ℝ) (Lf : Fin n → ℝ) (hA : Assumption1 G W f Lf)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ (1 + lamN W) / Lh Lf) (hα2 : α ≤ 1 / Lbar Lf)
    (xt : Stack n p) (hxt : ∀ y : Stack n p, xi α W f xt ≤ xi α W f y)
    (xs : E p) (hxs : xs ∈ Xstar f) :
    ∀ k : ℕ, rbar f (dgd W f α) xs (k + 1)
      ≤ rbar f (dgd W f α) xs k - α / (2 * Cconst xt xs ^ 2) * rbar f (dgd W f α) xs k ^ 2
        + α ^ 3 * D f Lf ^ 2 * Lh Lf ^ 2 / (2 * (1 - beta W) ^ 2) := by sorry

end YuanDGD.Sublinear
