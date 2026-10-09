-- Prove2me | Theorems.Thm_YuanDGD_Sublinear_theorem_2
-- name    : YuanDGD.Sublinear.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:20:33.122989+00:00
-- url     : https://prove2.me/theorems/aa9e6827-50da-4d6e-8123-5952250da291
-- title:
--   Theorem 2, pp. 10–11 — while r̄(k) > C√2·αL_hD/(1 − β), r̄(k + 1) ≤ r̄(k) − (α/(4C²))r̄²(k) and r̄(k) ≤ 4C²/(αk)
-- statement:
--   Let $n \ge 2$ agents run decentralized gradient descent (4) from $x_{(i)}(0) = 0$ under Assumption 1, with stepsize
--   $$0 < \alpha \le \min\Big\{\frac{1+\lambda_n(W)}{L_h},\ \frac{1}{L_{\bar f}}\Big\}.$$
--   Let $[\tilde x_{(i)}] \in \mathbb R^{np}$ be a minimizer of the Lyapunov function $\xi_\alpha$ (8), and let $x^* \in \mathcal X^*$ be a solution of (2). Let $C$ be the constant (17) built from them, $D$ the constant (10), $\bar r(k) = \bar f(\bar x(k)) - \bar f(x^*)$ the objective error of the mean iterate, and
--   $$T = C\sqrt2\cdot\frac{\alpha L_h D}{1-\beta}.$$
--   Then:
--
--   1. for every $k \ge 0$ with $\bar r(k) > T$,
--   $$\bar r(k+1) \le \bar r(k) - \frac{\alpha}{4C^2}\,\bar r(k)^2;$$
--   2. for every $k \ge 1$ such that $\bar r(j) > T$ for all $j < k$,
--   $$\bar r(k) \le \frac{4C^2}{\alpha k}.$$
--
--   In words: $\bar r(k)$ decreases at rate $O(1/(\alpha k))$ until it reaches the level $O(\alpha/(1-\beta))$. With a fixed stepsize, DGD thus behaves like centralized gradient descent with a sublinear rate, up to a neighbourhood whose size is proportional to the stepsize and inversely proportional to the spectral gap $1 - \beta$ of the network.
--
--   **Formalization Note.** The paper states the conclusions as $\bar r(k+1) \le \bar r(k) - O(\alpha\bar r^2(k))$ and $\bar r(k) \le O(1/(\alpha k))$. The explicit constants are those its proof fixes: the threshold condition "$(\alpha/(2C^2))\bar r^2(k) > 2\cdot\alpha^3D^2L_h^2/(2(1-\beta)^2)$, or equivalently $\bar r(k) > T$" lets the error term of the recursion $\bar r(k+1) \le \bar r(k) - (\alpha/(2C^2))\bar r^2(k) + \alpha^3D^2L_h^2/(2(1-\beta)^2)$ absorb half of the quadratic decrease, which gives $\alpha/(4C^2)$; "$1/\bar r(k)$ increases at $\Omega(\alpha k)$" is then $1/\bar r(k) \ge k\alpha/(4C^2)$, i.e. part 2. Part 2 requires the threshold at every earlier step ("while"). $C$ uses one fixed $x^* \in \mathcal X^*$ (on the page it is $x^*(k)$, which would make $C$ depend on $k$). The paper claims the minimizer set of $\xi_\alpha$ is nonempty from Assumption 1, which does not follow, so a minimizer is a hypothesis. When $C = 0$ both parts hold vacuously (then $T = 0$ and $\bar r(k) \le C\|\bar g(k)\| = 0$), so Lean's $a/0 = 0$ is harmless. $\alpha > 0$ is the reading of "stepsize"; $n \ge 2$ is part of the Assumption 1 structure.
-- source:
--   Yuan, Ling & Yin, On the Convergence of Decentralized Gradient Descent, arXiv:1310.7063v3, pp. 10–11, Theorem 2 (constants from its proof, p. 11)

import Mathlib
import Definitions.Def_YuanDGD_Sublinear_Setting

namespace YuanDGD.Sublinear

open YuanDGD.Linear

/-- Yuan–Ling–Yin, arXiv:1310.7063v3, Theorem 2, pp. 10–11, with the constants of its proof: under
Assumption 1, if `0 < α ≤ min{(1 + λₙ(W))/L_h, 1/L_f̄}`, `[x̃₍ᵢ₎]` minimizes `ξ_α` (8) and `x* ∈ X*`,
then with `C` of (17), `D` of (10) and `T = C√2 · αL_hD/(1 − β)`:
(i) whenever `r̄(k) > T`, `r̄(k + 1) ≤ r̄(k) − (α/(4C²))r̄²(k)`;
(ii) if `k ≥ 1` and `r̄(j) > T` for every `j < k`, then `r̄(k) ≤ 4C²/(αk)`. -/
theorem theorem_2 {n p : ℕ} (G : SimpleGraph (Fin n)) (W : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → E p → ℝ) (Lf : Fin n → ℝ) (hA : Assumption1 G W f Lf)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ (1 + lamN W) / Lh Lf) (hα2 : α ≤ 1 / Lbar Lf)
    (xt : Stack n p) (hxt : ∀ y : Stack n p, xi α W f xt ≤ xi α W f y)
    (xs : E p) (hxs : xs ∈ Xstar f) :
    (∀ k : ℕ, threshold W f Lf α (Cconst xt xs) < rbar f (dgd W f α) xs k →
      rbar f (dgd W f α) xs (k + 1)
        ≤ rbar f (dgd W f α) xs k - α / (4 * Cconst xt xs ^ 2) * rbar f (dgd W f α) xs k ^ 2) ∧
    (∀ k : ℕ, 1 ≤ k →
      (∀ j < k, threshold W f Lf α (Cconst xt xs) < rbar f (dgd W f α) xs j) →
      rbar f (dgd W f α) xs k ≤ 4 * Cconst xt xs ^ 2 / (α * k)) := by sorry

end YuanDGD.Sublinear
