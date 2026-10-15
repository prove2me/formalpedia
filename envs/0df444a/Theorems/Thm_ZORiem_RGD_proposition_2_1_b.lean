-- Prove2me | Theorems.Thm_ZORiem_RGD_proposition_2_1_b
-- name    : ZORiem.RGD.proposition_2_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:22.724442+00:00
-- url     : https://prove2.me/theorems/db041a67-277f-4f1f-a201-a535701a4ff2
-- title:
--   Proposition 2.1(b), p. 8, with L² — ‖grad f(x)‖² ≤ 2‖E g_µ(x)‖² + (µ²/2)L²(d+6)³
-- statement:
--   In the setting of Proposition 2.1(a) — $M\subseteq E$ a $C^1$ embedded submanifold of dimension $d$, $R$ a global retraction, $f$ differentiable and satisfying Assumption 2.1 with constant $L\ge0$, $x\in M$, $\mu>0$, and $g_\mu(x)$ the zeroth-order estimator (2.5) built from $u_0\sim N(0,I_n)$ — the estimator is integrable and
--
--   $$\|\operatorname{grad}f(x)\|^2\le2\,\big\|\mathbb E_{u_0}\big(g_\mu(x)\big)\big\|^2+\frac{\mu^2}{2}L^2(d+6)^3 .$$
--
--   This lower-bounds the size of the mean estimator by the true gradient, which is what lets the descent step of ZO-RGD make progress proportional to $\|\operatorname{grad}f(x)\|^2$.
--
--   **Formalization Note** The paper prints $\frac{\mu^2}{2}L(d+6)^3$. Its proof (p. 9) squares the remainder of Assumption 2.1, $\big(\tfrac L2\mu^2\|u\|^2\big)^2$, which gives $L^2$, and the printed form is false for large $L$: on $M=\mathbb R$ with $R_x(\eta)=x+\eta$, $x=0$, $\mu=1$ and $f=c\sin$ one has $L=c$, $\operatorname{grad}f(0)=c$, $\mathbb E g_1(0)=ce^{-1/2}$, and the printed inequality fails for $c>650$. The statement here has $L^2$. As in (a), "smooth" is weakened to differentiable and integrability of $g_\mu(x)$ is part of the conclusion.
-- source:
--   Li, Balasubramanian and Ma, arXiv:2003.11238v3, Proposition 2.1(b), p. 8 (proof p. 9)

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ZORiem_RGD_IsRetraction
import Definitions.Def_ZORiem_RGD_rgrad
import Definitions.Def_ZORiem_RGD_zoGrad

open MeasureTheory ProbabilityTheory ProjLikeRetr.Retractor
open scoped InnerProductSpace

namespace ZORiem.RGD

/-- Proposition 2.1(b), p. 8, with the factor `L²` its proof (p. 9) gives (the page prints `L`, which
is false for large `L`): under Assumption 2.1, at every `x ∈ M` and for every `µ > 0`, the estimator is
integrable and `‖grad f(x)‖² ≤ 2‖E g_µ(x)‖² + (µ²/2)L²(d+6)³`. -/
theorem proposition_2_1_b {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Set E) (d : ℕ) (hM : IsSubmanifold 1 d M)
    (R : E → E → E) (hR : IsRetraction M R)
    (f : E → ℝ) (hf : Differentiable ℝ f) (L : ℝ) (hL : 0 ≤ L)
    (hA21 : ∀ x ∈ M, ∀ η ∈ tangentSpace M x,
      |f (R x η) - f x - ⟪rgrad M f x, η⟫_ℝ| ≤ L / 2 * ‖η‖ ^ 2)
    (x : E) (hx : x ∈ M) (mu : ℝ) (hmu : 0 < mu) :
    Integrable (zoGrad M R f mu x) (stdGaussian E) ∧
    ‖rgrad M f x‖ ^ 2 ≤
      2 * ‖∫ u₀, zoGrad M R f mu x u₀ ∂(stdGaussian E)‖ ^ 2 +
        mu ^ 2 / 2 * L ^ 2 * ((d : ℝ) + 6) ^ 3 := by sorry

end ZORiem.RGD
