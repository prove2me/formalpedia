-- Prove2me | Theorems.Thm_YuanDGD_Linear_theorem_3
-- name    : YuanDGD.Linear.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:19:47.539432+00:00
-- url     : https://prove2.me/theorems/5ed0ee71-fc3f-4efc-aa6c-d3570a15468e
-- title:
--   Theorem 3, p. 12 — under (restricted) strong convexity and α ≤ min{(1 + λₙ(W))/L_h, c₁}, ‖ē(k + 1)‖² ≤ c₃²‖ē(k)‖² + c₄² for every δ > 0
-- statement:
--   Assume Assumption 1 for the agents' objectives $f_i$, the network and the mixing matrix $W$, that the solution set $\mathcal X^*$ of (2) is nonempty, and that $f=\sum_if_i$ is either strongly convex with modulus $\mu_f$ or restricted strongly convex with modulus $\nu_f$, with $c_1,c_2$ the corresponding constants of Lemma 3 for $\bar f$ ($\mu_{\bar f}=\mu_f/n$, $\nu_{\bar f}=\nu_f/n$, $L_{\bar f}=\frac1n\sum_iL_{f_i}$, $\theta\in[0,1]$ in the restricted case). Let the stepsize satisfy
--   $$
--   0<\alpha\le\min\Big\{\frac{1+\lambda_n(W)}{L_h},\ c_1\Big\},
--   $$
--   run DGD (4) from $0$, and let $x^*(k)=\mathrm{Proj}_{\mathcal X^*}(\bar x(k))$ and $\bar e(k)=\bar x(k)-x^*(k)$. Then for every $\delta>0$ and every $k\ge0$,
--   $$
--   \|\bar e(k+1)\|^2\le c_3^2\|\bar e(k)\|^2+c_4^2,\qquad c_3^2=1-\alpha c_2+\alpha\delta-\alpha^2\delta c_2,\quad c_4^2=\alpha^3(\alpha+\delta^{-1})\frac{L_h^2D^2}{(1-\beta)^2},
--   $$
--   with $D$ from (10).
--
--   The recursion is the core of the linear rate: unrolled at a suitable $\delta$ it gives geometric convergence of the mean to an $O(\alpha/(1-\beta))$ neighbourhood of $\mathcal X^*$.
--
--   **Formalization Note** $c_3^2$ and $c_4^2$ are the named expressions `c3sq`, `c4sq` (no square root is taken here). The projection $x^*(k)$ is any sequence of nearest points of $\mathcal X^*$ to $\bar x(k)$. $\alpha>0$ is the reading of $\alpha$ as a stepsize; the paper's "$=O(1/L_h)$" is a comment, not a hypothesis. Assumption 1 includes $n\ge2$.
-- source:
--   Yuan, Ling & Yin, On the Convergence of Decentralized Gradient Descent, arXiv:1310.7063v3, p. 12, Theorem 3

import Mathlib
import Definitions.Def_YuanDGD_Linear_Setting

open scoped InnerProductSpace

namespace YuanDGD.Linear

/-- Theorem 3, p. 12: under Assumption 1, if `f` is strongly convex or restricted strongly
convex (with `c₁, c₂` from Lemma 3) and `α ≤ min{(1 + λₙ(W))/L_h, c₁}`, then for every `δ > 0`
the solution error `ē(k) = x̄(k) − x*(k)` of DGD satisfies `‖ē(k + 1)‖² ≤ c₃²‖ē(k)‖² + c₄²`. -/
theorem theorem_3 {n p : ℕ} (G : SimpleGraph (Fin n)) (W : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → E p → ℝ) (Lf : Fin n → ℝ) (hA : Assumption1 G W f Lf)
    (hX : (Xstar f).Nonempty) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ (1 + lamN W) / Lh Lf)
    (c1 c2 : ℝ) (hc : Lemma3Consts f Lf c1 c2) (hα2 : α ≤ c1)
    (δ : ℝ) (hδ : 0 < δ)
    (xs : ℕ → E p) (hxs : ∀ k, IsProj (Xstar f) (xbar (dgd W f α) k) (xs k)) :
    ∀ k : ℕ, ‖xbar (dgd W f α) (k + 1) - xs (k + 1)‖ ^ 2 ≤
      c3sq α c2 δ * ‖xbar (dgd W f α) k - xs k‖ ^ 2 +
        c4sq α δ (Lh Lf) (D f Lf) (beta W) := by sorry

end YuanDGD.Linear
