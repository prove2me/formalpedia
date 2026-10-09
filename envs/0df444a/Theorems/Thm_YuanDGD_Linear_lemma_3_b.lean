-- Prove2me | Theorems.Thm_YuanDGD_Linear_lemma_3_b
-- name    : YuanDGD.Linear.lemma_3_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:19:42.536069+00:00
-- url     : https://prove2.me/theorems/b58a2500-d0f5-49c4-8a07-89b6cb7b374e
-- title:
--   Lemma 3 (b), p. 12 — restricted strongly convex case: c₁ = θ/L_f̄, c₂ = (1 − θ)ν_f̄ for any θ ∈ [0, 1]
-- statement:
--   Let $F:\mathbb R^p\to\mathbb R$ be convex and differentiable with $L$-Lipschitz gradient, $L>0$, and let $\mathcal X_F=\{z:\ F(z)\le F(y)\ \forall y\}$ be its set of minimizers. Suppose $F$ is restricted strongly convex with modulus $\nu>0$: $\langle\nabla F(x)-\nabla F(x^*),x-x^*\rangle\ge\nu\|x-x^*\|^2$ whenever $x^*=\mathrm{Proj}_{\mathcal X_F}(x)$. Then for every $\theta\in[0,1]$, every $x$ and its projection $x^*=\mathrm{Proj}_{\mathcal X_F}(x)$,
--   $$
--   \langle x-x^*,\nabla F(x)-\nabla F(x^*)\rangle\ \ge\ \frac{\theta}{L}\|\nabla F(x)-\nabla F(x^*)\|^2+(1-\theta)\nu\|x-x^*\|^2 .
--   $$
--
--   Applied to $F=\bar f$ with $L=L_{\bar f}$ and $\nu=\nu_{\bar f}$, this is case b) of Lemma 3 (citing [37, Lemma 2]): $c_1=\theta/L_{\bar f}$, $c_2=(1-\theta)\nu_{\bar f}$. It is the inequality Theorem 3 uses at $x=\bar x(k)$, $x^*=x^*(k)$.
--
--   **Formalization Note** The inequality is stated only for $x^*$ the projection of $x$ onto the solution set: the lemma's preamble says "$x^*\in\mathcal X^*$", but case b) does not hold at a solution other than the projection, and (7) and Theorem 3 use the projection. Convexity of $F$ is assumed; it holds for $\bar f$ (a mean of convex $f_i$) and is used by the cited proof. The statement is for a generic $F$; the paper applies it to $\bar f$.
-- source:
--   Yuan, Ling & Yin, On the Convergence of Decentralized Gradient Descent, arXiv:1310.7063v3, p. 12, Lemma 3 (b)

import Mathlib
import Definitions.Def_YuanDGD_Linear_Setting

open scoped InnerProductSpace

namespace YuanDGD.Linear

/-- Lemma 3 (b), p. 12 (citing [37, Lemma 2]): for a convex differentiable `F` with `L`-Lipschitz
gradient that is restricted strongly convex with modulus `ν` with respect to its set of
minimizers `X_F`, for every `θ ∈ [0, 1]`, every `x` and its projection `x*` onto `X_F`,
`⟨x − x*, ∇F(x) − ∇F(x*)⟩ ≥ (θ/L)‖∇F(x) − ∇F(x*)‖² + (1 − θ)ν‖x − x*‖²`. -/
theorem lemma_3_b {p : ℕ} (F : E p → ℝ) (hconv : ConvexOn ℝ Set.univ F)
    (hdiff : Differentiable ℝ F) (L : ℝ) (hL : 0 < L)
    (hlip : ∀ a b, ‖gradient F a - gradient F b‖ ≤ L * ‖a - b‖)
    (ν : ℝ) (hν : 0 < ν)
    (hRSC : ∀ x x' : E p, IsProj {z | ∀ y, F z ≤ F y} x x' →
      ν * ‖x - x'‖ ^ 2 ≤ ⟪gradient F x - gradient F x', x - x'⟫_ℝ)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x x' : E p, IsProj {z | ∀ y, F z ≤ F y} x x' →
      θ / L * ‖gradient F x - gradient F x'‖ ^ 2 + (1 - θ) * ν * ‖x - x'‖ ^ 2 ≤
        ⟪x - x', gradient F x - gradient F x'⟫_ℝ := by sorry

end YuanDGD.Linear
