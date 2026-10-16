-- Prove2me | Theorems.Thm_ZORiem_RSGD_lemma_3_1
-- name    : ZORiem.RSGD.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:02:40.97823+00:00
-- url     : https://prove2.me/theorems/e4488bb4-8790-4c92-87cf-ce5e3defdf6a
-- title:
--   Lemma 3.1, p. 16 — E‖ḡ_{µ,ξ}(x) − grad f(x)‖² ≤ µ²L²(d+6)³ + (8(d+4)/m)σ² + (8(d+4)/m)‖grad f(x)‖²
-- statement:
--   Let $\mathcal M \subseteq E$ be a $C^1$ embedded submanifold of dimension $d$ of a finite-dimensional real inner product space $E$, and $R$ a retraction on $\mathcal M$. Let $(\Xi, P_\xi)$ be a probability space and $F : E \times \Xi \to \mathbb R$ jointly measurable, and let $f : E \to \mathbb R$ be differentiable. Assume:
--
--   1. (**Assumption 2.1 for $F$, almost surely**) for $P_\xi$-almost every $\xi$, $F(\cdot, \xi)$ is differentiable and for all $x \in \mathcal M$, $\eta \in T_x\mathcal M$, $\big|F(R_x(\eta), \xi) - F(x, \xi) - \langle \operatorname{grad} F(x, \xi), \eta\rangle\big| \le \frac L2\|\eta\|^2$, with a constant $L \ge 0$;
--   2. (**Assumption 2.3**) for every $x \in \mathcal M$: $F(x,\cdot)$ and $\operatorname{grad}F(x,\cdot)$ are integrable, $\mathbb E_\xi F(x,\xi) = f(x)$, $\mathbb E_\xi \operatorname{grad}F(x,\xi) = \operatorname{grad} f(x)$, and $\mathbb E_\xi\|\operatorname{grad}F(x,\xi) - \operatorname{grad}f(x)\|^2 \le \sigma^2$.
--
--   Here $\operatorname{grad}F(x,\xi)$ is the Riemannian gradient of $F(\cdot,\xi)$. Let $x \in \mathcal M$, $\mu > 0$, $m \ge 1$, and let $\bar g_{\mu,\xi}(x)$ be the mini-batch estimator (3.6) built from $m$ i.i.d. pairs $(u_{0,i}, \xi_i)$ with $u_{0,i} \sim \mathcal N(0,I)$ independent of $\xi_i \sim P_\xi$. Then
--
--   $$\mathbb E\,\|\bar g_{\mu,\xi}(x) - \operatorname{grad} f(x)\|^2 \le \mu^2L^2(d + 6)^3 + \frac{8(d+4)}{m}\sigma^2 + \frac{8(d+4)}{m}\|\operatorname{grad} f(x)\|^2,$$
--
--   the expectation being over all $m$ Gaussian vectors and all $m$ noise samples.
--
--   The bound separates a smoothing bias ($\mu^2$), a noise term and a term proportional to the squared gradient; both of the latter decrease as $1/m$. Theorem 3.2 uses it with $m \ge 16(d+4)$ so that the gradient term is absorbed by the descent of one step.
--
--   **Formalization Note** The expectation is the lower Lebesgue integral of $\|\bar g_{\mu,\xi}(x) - \operatorname{grad}f(x)\|^2$ against `batchLaw E Pξ m`, compared with `ENNReal.ofReal` of the right-hand side, so it cannot be a junk value. The paper's last step of the proof (Appendix C) needs $m \ge 2$, but the bound holds for every $m \ge 1$, which is what is stated. $f$ is given together with $F$ and tied to it on $\mathcal M$ by Assumption 2.3; Assumption 2.1 for $f$ itself is not assumed (the paper notes it follows). The smoothing parameter is written `mu`; the noise law is `Pξ`.
-- source:
--   Li, Balasubramanian and Ma, arXiv:2003.11238v3, Lemma 3.1, (3.8), p. 16 (proof Appendix C, pp. 31–32); Assumption 2.3, p. 10; (3.5)–(3.6), p. 16

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ZORiem_RGD_IsRetraction
import Definitions.Def_ZORiem_RGD_rgrad
import Definitions.Def_ZORiem_RSGD_zoGradBatch

open MeasureTheory ProbabilityTheory ProjLikeRetr.Retractor
open scoped InnerProductSpace

namespace ZORiem.RSGD

theorem lemma_3_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Set E) (d : ℕ) (hM : IsSubmanifold 1 d M)
    (R : E → E → E) (hR : ZORiem.RGD.IsRetraction M R)
    {Ξ : Type*} [MeasurableSpace Ξ] (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ]
    (F : E → Ξ → ℝ) (hFmeas : Measurable (Function.uncurry F))
    (f : E → ℝ) (hf : Differentiable ℝ f) (L : ℝ) (hL : 0 ≤ L)
    (hF21 : ∀ᵐ ξ ∂Pξ, Differentiable ℝ (fun y => F y ξ) ∧
      ∀ x ∈ M, ∀ η ∈ tangentSpace M x,
        |F (R x η) ξ - F x ξ - ⟪ZORiem.RGD.rgrad M (fun y => F y ξ) x, η⟫_ℝ| ≤ L / 2 * ‖η‖ ^ 2)
    (σ : ℝ)
    (hA23 : ∀ x ∈ M,
      Integrable (fun ξ => F x ξ) Pξ ∧ ∫ ξ, F x ξ ∂Pξ = f x ∧
      Integrable (fun ξ => ZORiem.RGD.rgrad M (fun y => F y ξ) x) Pξ ∧
      ∫ ξ, ZORiem.RGD.rgrad M (fun y => F y ξ) x ∂Pξ = ZORiem.RGD.rgrad M f x ∧
      ∫⁻ ξ, ENNReal.ofReal (‖ZORiem.RGD.rgrad M (fun y => F y ξ) x - ZORiem.RGD.rgrad M f x‖ ^ 2) ∂Pξ ≤
        ENNReal.ofReal (σ ^ 2))
    (x : E) (hx : x ∈ M) (mu : ℝ) (hmu : 0 < mu) (m : ℕ) (hm : 1 ≤ m) :
    ∫⁻ s, ENNReal.ofReal (‖zoGradBatch M R F mu m x s - ZORiem.RGD.rgrad M f x‖ ^ 2) ∂(batchLaw E Pξ m) ≤
      ENNReal.ofReal (mu ^ 2 * L ^ 2 * ((d : ℝ) + 6) ^ 3 + 8 * ((d : ℝ) + 4) / m * σ ^ 2 +
        8 * ((d : ℝ) + 4) / m * ‖ZORiem.RGD.rgrad M f x‖ ^ 2) := by sorry

end ZORiem.RSGD
