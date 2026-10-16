-- Prove2me | Theorems.Thm_ZORiem_RSGD_proposition_2_1_a
-- name    : ZORiem.RSGD.proposition_2_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:42.791904+00:00
-- url     : https://prove2.me/theorems/f117d7c4-037b-464b-a92d-3ea66adc39dc
-- title:
--   Proposition 2.1(a), p. 8 — the bias of the zeroth-order Riemannian gradient estimator is at most (µL/2)(d + 3)^{3/2}
-- statement:
--   Let $\mathcal M \subseteq E$ be a $C^1$ embedded submanifold of dimension $d$ of a finite-dimensional real inner product space $E$, and $R$ a retraction on $\mathcal M$ (defined on all of each tangent space). Let $f : E \to \mathbb R$ be differentiable and satisfy **Assumption 2.1** ($L$-retraction-smoothness) with a constant $L \ge 0$:
--
--   $$\big|f(R_x(\eta)) - f(x) - \langle \operatorname{grad} f(x), \eta\rangle\big| \le \frac L2\|\eta\|^2 \qquad \text{for all } x \in \mathcal M,\ \eta \in T_x\mathcal M .$$
--
--   Let $x \in \mathcal M$, $\mu > 0$, and let $g_\mu(x)$ be the zeroth-order estimator (2.5) with $u_0 \sim \mathcal N(0, I)$. Then $g_\mu(x)$ is integrable in $u_0$ and
--
--   $$\big\|\mathbb E_{u_0}(g_\mu(x)) - \operatorname{grad} f(x)\big\| \le \frac{\mu L}{2}(d + 3)^{3/2}.$$
--
--   The bias vanishes linearly in the smoothing parameter and grows only with the manifold dimension $d$. It is one of the two ingredients (with the second-moment bound) of the error bound for the mini-batch estimator, Lemma 3.1.
--
--   **Formalization Note** $\mathcal M$ is `IsSubmanifold 1 d M` (published), which ties $d$ to $\mathcal M$: every tangent space has dimension $d$. The paper's "smooth" $f$ is weakened to differentiable, which is all (2.3) needs. Integrability of $u_0 \mapsto g_\mu(x)$ is part of the conclusion, so the expectation is a genuine one.
-- source:
--   Li, Balasubramanian and Ma, arXiv:2003.11238v3, Proposition 2.1(a), p. 8

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ZORiem_RGD_IsRetraction
import Definitions.Def_ZORiem_RGD_rgrad
import Definitions.Def_ZORiem_RGD_zoGrad

open MeasureTheory ProbabilityTheory ProjLikeRetr.Retractor
open scoped InnerProductSpace

namespace ZORiem.RSGD

theorem proposition_2_1_a {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Set E) (d : ℕ) (hM : IsSubmanifold 1 d M)
    (R : E → E → E) (hR : ZORiem.RGD.IsRetraction M R)
    (f : E → ℝ) (hf : Differentiable ℝ f) (L : ℝ) (hL : 0 ≤ L)
    (hA21 : ∀ x ∈ M, ∀ η ∈ tangentSpace M x,
      |f (R x η) - f x - ⟪ZORiem.RGD.rgrad M f x, η⟫_ℝ| ≤ L / 2 * ‖η‖ ^ 2)
    (x : E) (hx : x ∈ M) (mu : ℝ) (hmu : 0 < mu) :
    Integrable (ZORiem.RGD.zoGrad M R f mu x) (stdGaussian E) ∧
      ‖∫ u₀, ZORiem.RGD.zoGrad M R f mu x u₀ ∂(stdGaussian E) - ZORiem.RGD.rgrad M f x‖ ≤
        mu * L / 2 * ((d : ℝ) + 3) ^ ((3 : ℝ) / 2) := by sorry

end ZORiem.RSGD
