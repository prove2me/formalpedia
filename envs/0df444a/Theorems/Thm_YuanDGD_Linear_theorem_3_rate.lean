-- Prove2me | Theorems.Thm_YuanDGD_Linear_theorem_3_rate
-- name    : YuanDGD.Linear.theorem_3_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:19:49.986129+00:00
-- url     : https://prove2.me/theorems/afc82f79-9f2c-44a1-923c-293c705f9055
-- title:
--   Theorem 3, "in particular", pp. 12–13 — with δ = c₂/(2(1 − αc₂)), ‖ē(k)‖ ≤ c₃ᵏ‖ē(0)‖ + c₄/√(1 − c₃²), c₃ = √(1 − αc₂/2)
-- statement:
--   Under the hypotheses of Theorem 3 (Assumption 1, $\mathcal X^*\ne\emptyset$, $f$ strongly or restricted strongly convex with Lemma 3's constants $c_1,c_2$, and $0<\alpha\le\min\{(1+\lambda_n(W))/L_h,\,c_1\}$), assume moreover $c_2>0$. Set $\delta=c_2/(2(1-\alpha c_2))$, so that
--   $$
--   c_3=\sqrt{1-\frac{\alpha c_2}{2}},\qquad c_4=\sqrt{\alpha^3(\alpha+\delta^{-1})\frac{L_h^2D^2}{(1-\beta)^2}} .
--   $$
--   Then the solution error $\bar e(k)=\bar x(k)-x^*(k)$ of DGD satisfies, for every $k\ge0$,
--   $$
--   \|\bar e(k)\|\le c_3^k\,\|\bar e(0)\|+\frac{c_4}{\sqrt{1-c_3^2}} .
--   $$
--
--   This is the "in particular" of Theorem 3: the mean $\bar x(k)$ converges geometrically, at rate $c_3<1$, to a neighbourhood of the solution set whose radius $c_4/\sqrt{1-c_3^2}=\frac{\alpha L_hD}{1-\beta}\sqrt{4/c_2^2-2\alpha/c_2}$ is $O(\alpha/(1-\beta))$.
--
--   **Formalization Note** The page writes the additive term as $O(\alpha/(1-\beta))$; the item states the explicit $c_4/\sqrt{1-c_3^2}$ that the proof derives on p. 13 and that Corollary 1 uses. $c_2>0$ is the page's own requirement for $\delta>0$ and $c_3\in(0,1)$ (it excludes $\theta=1$ in the restricted case).
-- source:
--   Yuan, Ling & Yin, On the Convergence of Decentralized Gradient Descent, arXiv:1310.7063v3, p. 12, Theorem 3 ("In particular"), with the constant of its proof, p. 13

import Mathlib
import Definitions.Def_YuanDGD_Linear_Setting

open scoped InnerProductSpace

namespace YuanDGD.Linear

/-- Theorem 3, "in particular", p. 12, with the explicit constant of its proof (p. 13): with
`δ = c₂/(2(1 − αc₂))`, `c₃ = √(1 − αc₂/2)` and `c₄ = √(c₄²)`, the solution error of DGD satisfies
`‖ē(k)‖ ≤ c₃ᵏ‖ē(0)‖ + c₄/√(1 − c₃²)` for every `k`. -/
theorem theorem_3_rate {n p : ℕ} (G : SimpleGraph (Fin n)) (W : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → E p → ℝ) (Lf : Fin n → ℝ) (hA : Assumption1 G W f Lf)
    (hX : (Xstar f).Nonempty) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ (1 + lamN W) / Lh Lf)
    (c1 c2 : ℝ) (hc : Lemma3Consts f Lf c1 c2) (hα2 : α ≤ c1) (hc2 : 0 < c2)
    (xs : ℕ → E p) (hxs : ∀ k, IsProj (Xstar f) (xbar (dgd W f α) k) (xs k)) :
    ∀ k : ℕ, ‖xbar (dgd W f α) k - xs k‖ ≤
      c3 α c2 ^ k * ‖xbar (dgd W f α) 0 - xs 0‖ +
        c4 α c2 (Lh Lf) (D f Lf) (beta W) / Real.sqrt (1 - c3 α c2 ^ 2) := by sorry

end YuanDGD.Linear
