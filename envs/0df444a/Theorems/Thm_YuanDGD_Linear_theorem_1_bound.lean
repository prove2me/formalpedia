-- Prove2me | Theorems.Thm_YuanDGD_Linear_theorem_1_bound
-- name    : YuanDGD.Linear.theorem_1_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:19:23.178893+00:00
-- url     : https://prove2.me/theorems/6b39f908-c6d5-4e88-b8f6-1253934b50c2
-- title:
--   Theorem 1, (10), p. 7 — under α ≤ (1 + λₙ(W))/L_h the stacked gradient of DGD satisfies ‖h(k)‖ ≤ D
-- statement:
--   Let $n$ agents with local objectives $f_i:\mathbb R^p\to\mathbb R$ and mixing matrix $W$ satisfy Assumption 1 (convex, bounded below, $L_{f_i}$-smooth $f_i$; connected network; symmetric doubly stochastic $W$ with $\beta<1$; $n\ge2$). Let $L_h=\max_iL_{f_i}$, $\lambda_n(W)$ the smallest eigenvalue of $W$, and run DGD (4) from $x_{(i)}(0)=0$ with a stepsize $\alpha>0$ satisfying
--   $$
--   \alpha\le\frac{1+\lambda_n(W)}{L_h}. \qquad (9)
--   $$
--   Then the stacked gradient $h(k)=[\nabla f_1(x_{(1)}(k));\dots;\nabla f_n(x_{(n)}(k))]$ obeys, for every $k\ge0$,
--   $$
--   \|h(k)\|\le D=\sqrt{2L_h\sum_{i=1}^n\big(f_i(0)-f_i^o\big)},
--   $$
--   where $f_i^o=\inf f_i$ and the norm is the Euclidean norm of $\mathbb R^{np}$.
--
--   The bound says that bounded gradients along DGD are a consequence of the stepsize condition rather than an assumption; it feeds Lemmas 1 and 2 with $D$ as the gradient bound.
--
--   **Formalization Note** Only the bound (10) of Theorem 1 is stated; the theorem's first sentence (convergence of $x_{(i)}(k)$) is not part of this item. The page states (10) for $k=1,2,\dots$; the proof of Lemma 1 uses it at $k=0$ as well, and it holds there by the same argument, so it is stated for every $k\ge0$. $f_i^o$ is the infimum of $f_i$ (see the Setting module). The hypothesis $\alpha>0$ is the reading of $\alpha$ as a stepsize.
-- source:
--   Yuan, Ling & Yin, On the Convergence of Decentralized Gradient Descent, arXiv:1310.7063v3, p. 7, Theorem 1, (9), (10)

import Mathlib
import Definitions.Def_YuanDGD_Linear_Setting

open scoped InnerProductSpace

namespace YuanDGD.Linear

/-- Theorem 1, (10), p. 7: under Assumption 1 and the stepsize condition (9), the stacked
gradient of DGD started from zero satisfies `‖h(k)‖ ≤ D` for every `k ≥ 0`. -/
theorem theorem_1_bound {n p : ℕ} (G : SimpleGraph (Fin n)) (W : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → E p → ℝ) (Lf : Fin n → ℝ) (hA : Assumption1 G W f Lf)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ (1 + lamN W) / Lh Lf) :
    ∀ k : ℕ, ‖hvec f (dgd W f α) k‖ ≤ D f Lf := by sorry

end YuanDGD.Linear
