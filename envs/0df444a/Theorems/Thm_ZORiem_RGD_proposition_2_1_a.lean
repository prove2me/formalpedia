-- Prove2me | Theorems.Thm_ZORiem_RGD_proposition_2_1_a
-- name    : ZORiem.RGD.proposition_2_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:18.612097+00:00
-- url     : https://prove2.me/theorems/14c3c3bd-5acb-4e23-a1b5-417c64e0a292
-- title:
--   Proposition 2.1(a), p. 8 — bias of the zeroth-order Riemannian gradient: ‖E g_µ(x) − grad f(x)‖ ≤ (µL/2)(d+3)^{3/2}
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, $M\subseteq E$ a $C^1$ embedded submanifold of dimension $d$ with tangent spaces $T_xM$, and $R$ a retraction on $M$ defined on all of each $T_xM$. Let $f:E\to\mathbb R$ be differentiable, with Riemannian gradient $\operatorname{grad}f(x)=\operatorname{Proj}_{T_xM}\nabla f(x)$, and suppose $f$ satisfies **Assumption 2.1** with a constant $L\ge0$:
--
--   $$\big|f(R_x(\eta))-f(x)-\langle\operatorname{grad}f(x),\eta\rangle\big|\le\frac L2\|\eta\|^2\qquad\text{for all }x\in M,\ \eta\in T_xM .$$
--
--   Let $x\in M$, $\mu>0$, and let $g_\mu(x)=\frac{f(R_x(\mu u))-f(x)}{\mu}u$ with $u=P_xu_0$, $u_0\sim N(0,I_n)$, be the estimator (2.5). Then $g_\mu(x)$ is integrable and
--
--   $$\big\|\mathbb E_{u_0}\big(g_\mu(x)\big)-\operatorname{grad}f(x)\big\|\le\frac{\mu L}{2}(d+3)^{3/2}.$$
--
--   The estimator is biased, and the bias is of order $\mu$ with a constant depending on the manifold dimension $d$ only; this is the first of the three estimates on which the convergence analysis of ZO-RGD rests.
--
--   **Formalization Note** The paper's "smooth" $f$ is replaced by differentiable $f$, which is all that the definition (2.3) of $\operatorname{grad}f$ needs; this strengthens the statement. Integrability of $g_\mu(x)$ is part of the conclusion so that the Bochner expectation is never the junk value $0$. $d$ is tied to $M$ by the coordinate-slice predicate `IsSubmanifold 1 d M`.
-- source:
--   Li, Balasubramanian and Ma, arXiv:2003.11238v3, Proposition 2.1(a), p. 8

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ZORiem_RGD_IsRetraction
import Definitions.Def_ZORiem_RGD_rgrad
import Definitions.Def_ZORiem_RGD_zoGrad

open MeasureTheory ProbabilityTheory ProjLikeRetr.Retractor
open scoped InnerProductSpace

namespace ZORiem.RGD

/-- Proposition 2.1(a), p. 8: under Assumption 2.1 (with constant `L ≥ 0`, for all `x ∈ M` and all
`η ∈ T_xM`), at every `x ∈ M` and for every `µ > 0` the estimator `g_µ(x)` of (2.5) is integrable in
the Gaussian draw `u₀ ∼ N(0, I_n)` and its bias satisfies `‖E g_µ(x) − grad f(x)‖ ≤ (µL/2)(d+3)^{3/2}`. -/
theorem proposition_2_1_a {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Set E) (d : ℕ) (hM : IsSubmanifold 1 d M)
    (R : E → E → E) (hR : IsRetraction M R)
    (f : E → ℝ) (hf : Differentiable ℝ f) (L : ℝ) (hL : 0 ≤ L)
    (hA21 : ∀ x ∈ M, ∀ η ∈ tangentSpace M x,
      |f (R x η) - f x - ⟪rgrad M f x, η⟫_ℝ| ≤ L / 2 * ‖η‖ ^ 2)
    (x : E) (hx : x ∈ M) (mu : ℝ) (hmu : 0 < mu) :
    Integrable (zoGrad M R f mu x) (stdGaussian E) ∧
    ‖∫ u₀, zoGrad M R f mu x u₀ ∂(stdGaussian E) - rgrad M f x‖ ≤
      mu * L / 2 * ((d : ℝ) + 3) ^ ((3 : ℝ) / 2) := by sorry

end ZORiem.RGD
