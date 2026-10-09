-- Prove2me | Theorems.Thm_YuanDGD_Sublinear_thm2_descent
-- name    : YuanDGD.Sublinear.thm2_descent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:20:39.427803+00:00
-- url     : https://prove2.me/theorems/22de0f09-d372-4fc5-8b55-20cf809222c4
-- title:
--   Proof of Theorem 2, p. 11 — r̄(k + 1) ≤ r̄(k) − (α/2)‖ḡ(k)‖² + α³D²L_h²/(2(1 − β)²)
-- statement:
--   Under Assumption 1, let
--   $$0 < \alpha \le \min\Big\{\frac{1+\lambda_n(W)}{L_h},\ \frac{1}{L_{\bar f}}\Big\}, \qquad L_{\bar f} = \frac1n\sum_{i=1}^n L_{f_i},$$
--   and let $x^* \in \mathcal X^*$. With $\bar r(k) = \bar f(\bar x(k)) - \bar f(x^*)$ the objective error of the DGD mean iterate, for every $k \ge 0$
--   $$\bar r(k+1) \le \bar r(k) - \frac{\alpha}{2}\|\bar g(k)\|^2 + \frac{\alpha^3 D^2 L_h^2}{2(1-\beta)^2},$$
--   where $\bar g(k) = \frac1n\sum_i \nabla f_i(\bar x(k)) = \nabla\bar f(\bar x(k))$ and $D$ is the constant (10).
--
--   This is the descent inequality for the mean iterate viewed as inexact gradient descent on $\bar f$: a decrease proportional to the squared gradient, minus an error of order $\alpha^3/(1-\beta)^2$ coming from the disagreement between agents.
--
--   **Formalization Note.** This is the display of the proof of Theorem 2 obtained with Young's parameter $\delta = 1$. $\alpha > 0$ is the reading of "stepsize".
-- source:
--   Yuan, Ling & Yin, On the Convergence of Decentralized Gradient Descent, arXiv:1310.7063v3, p. 11, proof of Theorem 2, display after Young's inequality

import Mathlib
import Definitions.Def_YuanDGD_Sublinear_Setting

namespace YuanDGD.Sublinear

open YuanDGD.Linear

/-- Yuan–Ling–Yin, arXiv:1310.7063v3, proof of Theorem 2, p. 11, the display after Young's inequality
(with `δ = 1`): under Assumption 1, if `0 < α ≤ min{(1 + λₙ(W))/L_h, 1/L_f̄}` and `x* ∈ X*`, then
`r̄(k + 1) ≤ r̄(k) − (α/2)‖ḡ(k)‖² + α³D²L_h²/(2(1 − β)²)` for every `k`. -/
theorem thm2_descent {n p : ℕ} (G : SimpleGraph (Fin n)) (W : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → E p → ℝ) (Lf : Fin n → ℝ) (hA : Assumption1 G W f Lf)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ (1 + lamN W) / Lh Lf) (hα2 : α ≤ 1 / Lbar Lf)
    (xs : E p) (hxs : xs ∈ Xstar f) :
    ∀ k : ℕ, rbar f (dgd W f α) xs (k + 1)
      ≤ rbar f (dgd W f α) xs k - α / 2 * ‖gbar f (dgd W f α) k‖ ^ 2
        + α ^ 3 * D f Lf ^ 2 * Lh Lf ^ 2 / (2 * (1 - beta W) ^ 2) := by sorry

end YuanDGD.Sublinear
