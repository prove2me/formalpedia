-- Prove2me | Theorems.Thm_YuanDGD_Linear_corollary_1
-- name    : YuanDGD.Linear.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:20:06.686972+00:00
-- url     : https://prove2.me/theorems/eabfb7f8-5e63-42a8-8fda-27a2b8c50711
-- title:
--   Corollary 1, p. 14 — every agent satisfies ‖x₍ᵢ₎(k) − x*(k)‖ ≤ c₃ᵏ‖x*(0)‖ + c₄/√(1 − c₃²) + αD/(1 − β)
-- statement:
--   Consider $n\ge2$ agents with objectives $f_i:\mathbb R^p\to\mathbb R$, a network $G$ and a mixing matrix $W$ satisfying Assumption 1: each $f_i$ is convex, differentiable, bounded below, with $L_{f_i}$-Lipschitz gradient ($L_{f_i}>0$); $G$ is connected, $w_{ij}\ne0$ only for $i=j$ or neighbours $i,j$, $W$ is symmetric and doubly stochastic, and $\beta=\max\{|\lambda_2(W)|,|\lambda_n(W)|\}<1$. Assume the solution set $\mathcal X^*$ of $\min_x\sum_if_i(x)$ is nonempty, and that $f=\sum_if_i$ is either strongly convex with modulus $\mu_f$ or restricted strongly convex with modulus $\nu_f$, with $c_1,c_2$ the constants of Lemma 3 for $\bar f=f/n$, and $c_2>0$. Let the stepsize satisfy
--   $$
--   0<\alpha<\min\Big\{\frac{1+\lambda_n(W)}{L_h},\ c_1\Big\},\qquad L_h=\max_iL_{f_i},
--   $$
--   and let $x_{(i)}(k)$ be the DGD iterates (4) from $x_{(i)}(0)=0$, $\bar x(k)$ their mean and $x^*(k)=\mathrm{Proj}_{\mathcal X^*}(\bar x(k))$. Then for every $k\ge0$ and every agent $i$,
--   $$
--   \|x_{(i)}(k)-x^*(k)\|\le c_3^k\,\|x^*(0)\|+\frac{c_4}{\sqrt{1-c_3^2}}+\frac{\alpha D}{1-\beta},
--   $$
--   where $D=\sqrt{2L_h\sum_i(f_i(0)-f_i^o)}$, $c_3=\sqrt{1-\alpha c_2/2}$ and $c_4=\sqrt{\alpha^3(\alpha+\delta^{-1})L_h^2D^2/(1-\beta)^2}$ with $\delta=c_2/(2(1-\alpha c_2))$ are the constants of Theorem 3.
--
--   Every agent's iterate therefore converges geometrically to an $O(\alpha/(1-\beta))$ neighbourhood of the solution set: with a fixed stepsize, DGD reaches only approximate optimality, and the radius depends on the stepsize and the spectral gap $1-\beta$ of the network.
--
--   **Formalization Note** $c_3,c_4$ are taken at Theorem 3's particular $\delta=c_2/(2(1-\alpha c_2))$, the only choice for which the page establishes $c_3<1$; $c_2>0$ is the page's own requirement for this (it excludes $\theta=1$ in the restricted case). Both stepsize bounds are strict, as printed in the corollary. $\|x^*(0)\|$ is the page's; it equals $\|\bar e(0)\|$ because $\bar x(0)=0$. The projections $x^*(k)$ are any sequence of nearest points of $\mathcal X^*$ to $\bar x(k)$. $\alpha>0$ is the reading of $\alpha$ as a stepsize, and $n\ge2$ is part of Assumption 1 here because $\lambda_2(W)$ needs two agents.
-- source:
--   Yuan, Ling & Yin, On the Convergence of Decentralized Gradient Descent, arXiv:1310.7063v3, p. 14, Corollary 1

import Mathlib
import Definitions.Def_YuanDGD_Linear_Setting

open scoped InnerProductSpace

namespace YuanDGD.Linear

/-- Corollary 1, p. 14: under Assumption 1, if `f` is strongly convex or restricted strongly
convex (with `c₁, c₂` from Lemma 3, `c₂ > 0`) and `α < min{(1 + λₙ(W))/L_h, c₁}`, every agent of
DGD satisfies `‖x₍ᵢ₎(k) − x*(k)‖ ≤ c₃ᵏ‖x*(0)‖ + c₄/√(1 − c₃²) + αD/(1 − β)`, with `c₃, c₄` the
constants of Theorem 3 at `δ = c₂/(2(1 − αc₂))`. -/
theorem corollary_1 {n p : ℕ} (G : SimpleGraph (Fin n)) (W : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → E p → ℝ) (Lf : Fin n → ℝ) (hA : Assumption1 G W f Lf)
    (hX : (Xstar f).Nonempty) (α : ℝ) (hα : 0 < α) (hα1 : α < (1 + lamN W) / Lh Lf)
    (c1 c2 : ℝ) (hc : Lemma3Consts f Lf c1 c2) (hα2 : α < c1) (hc2 : 0 < c2)
    (xs : ℕ → E p) (hxs : ∀ k, IsProj (Xstar f) (xbar (dgd W f α) k) (xs k)) :
    ∀ (k : ℕ) (i : Fin n), ‖dgd W f α k i - xs k‖ ≤
      c3 α c2 ^ k * ‖xs 0‖ +
        c4 α c2 (Lh Lf) (D f Lf) (beta W) / Real.sqrt (1 - c3 α c2 ^ 2) +
          α * D f Lf / (1 - beta W) := by sorry

end YuanDGD.Linear
