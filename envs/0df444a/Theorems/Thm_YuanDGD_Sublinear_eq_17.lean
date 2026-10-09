-- Prove2me | Theorems.Thm_YuanDGD_Sublinear_eq_17
-- name    : YuanDGD.Sublinear.eq_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:20:31.279967+00:00
-- url     : https://prove2.me/theorems/84788117-a300-4385-9b36-7b7a299373fb
-- title:
--   (17), proof of Theorem 2, p. 11 — d(k) ≤ d(0) and ‖x̄(k) − x*‖ ≤ C
-- statement:
--   Under Assumption 1, let $0 < \alpha \le (1+\lambda_n(W))/L_h$ and let $[\tilde x_{(i)}] \in \mathbb R^{np}$ be a minimizer of the Lyapunov function $\xi_\alpha$ (8). Let $x^* \in \mathbb R^p$ be any point. Then the DGD iterates (4) from $0$ satisfy, for every $k \ge 0$,
--   $$d(k) := \|[x_{(i)}(k) - \tilde x_{(i)}]\| \le d(0)$$
--   and
--   $$\|\bar x(k) - x^*\| \le C := \frac{1}{\sqrt n}\Big(\|[x_{(i)}(0) - \tilde x_{(i)}]\| + \|[\tilde x_{(i)} - x^*]\|\Big).$$
--
--   When $x^* \in \mathcal X^*$, the solution error $\bar e(k) = \bar x(k) - \mathrm{Proj}_{\mathcal X^*}(\bar x(k))$ then satisfies $\|\bar e(k)\| \le \|\bar x(k) - x^*\| \le C$, which is the paper's (17). The constant $C$ bounds the distance of the mean iterate to a solution uniformly in $k$, and Theorem 2's proof uses it to turn the descent inequality into a recursion in $\bar r(k)$ alone.
--
--   **Formalization Note.** The paper asserts that the minimizer set of $\xi_\alpha$ is nonempty because each $f_i$ has a minimizer; that does not follow from Assumption 1 (a convex function bounded below need not attain its infimum), so a minimizer $[\tilde x_{(i)}]$ is taken as a hypothesis. On the page $x^*$ in (17) is $x^*(k)$, which would make $C$ depend on $k$; here $x^*$ is one fixed point, chosen before $k$, and membership in $\mathcal X^*$ is not needed for this bound.
-- source:
--   Yuan, Ling & Yin, On the Convergence of Decentralized Gradient Descent, arXiv:1310.7063v3, p. 11, proof of Theorem 2, (17)

import Mathlib
import Definitions.Def_YuanDGD_Sublinear_Setting

namespace YuanDGD.Sublinear

open YuanDGD.Linear

/-- Yuan–Ling–Yin, arXiv:1310.7063v3, (17), proof of Theorem 2, p. 11: under Assumption 1, if
`0 < α ≤ (1 + λₙ(W))/L_h` and `[x̃₍ᵢ₎]` minimizes the Lyapunov function `ξ_α` (8), then
`d(k) = ‖[x₍ᵢ₎(k) − x̃₍ᵢ₎]‖` is at most `d(0)`, and for any `x*` the mean satisfies
`‖x̄(k) − x*‖ ≤ C = (1/√n)(‖[x₍ᵢ₎(0) − x̃₍ᵢ₎]‖ + ‖[x̃₍ᵢ₎ − x*]‖)`, for every `k`. -/
theorem eq_17 {n p : ℕ} (G : SimpleGraph (Fin n)) (W : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → E p → ℝ) (Lf : Fin n → ℝ) (hA : Assumption1 G W f Lf)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ (1 + lamN W) / Lh Lf)
    (xt : Stack n p) (hxt : ∀ y : Stack n p, xi α W f xt ≤ xi α W f y) (xs : E p) :
    ∀ k : ℕ, ‖dgd W f α k - xt‖ ≤ ‖dgd W f α 0 - xt‖ ∧
      ‖xbar (dgd W f α) k - xs‖ ≤ Cconst xt xs := by sorry

end YuanDGD.Sublinear
