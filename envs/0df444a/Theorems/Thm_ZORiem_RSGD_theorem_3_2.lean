-- Prove2me | Theorems.Thm_ZORiem_RSGD_theorem_3_2
-- name    : ZORiem.RSGD.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:03:35.598976+00:00
-- url     : https://prove2.me/theorems/642de29f-8874-4606-9b1b-035e8a3ae615
-- title:
--   Theorem 3.2, p. 17 — ZO-RSGD with step 1/L and m ≥ 16(d+4): (1/(N+1))Σ E‖grad f(x_k)‖² ≤ 4L(f(x₀) − f(x*))/(N+1) + 2µ²L²(d+6)³ + 16(d+4)σ²/m
-- statement:
--   Let $\mathcal M \subseteq E$ be a $C^1$ embedded submanifold of dimension $d$ of a finite-dimensional real inner product space $E$, and $R$ a retraction on $\mathcal M$. Let $(\Xi, P_\xi)$ be a probability space, $F : E \times \Xi \to \mathbb R$ jointly measurable and $f : E \to \mathbb R$ differentiable, and let $L > 0$ and $\sigma \in \mathbb R$ be such that
--
--   1. (**Assumption 2.1 for $F$, almost surely**) for $P_\xi$-almost every $\xi$, $F(\cdot,\xi)$ is differentiable and $\big|F(R_x(\eta),\xi) - F(x,\xi) - \langle\operatorname{grad}F(x,\xi),\eta\rangle\big| \le \frac L2\|\eta\|^2$ for all $x \in \mathcal M$, $\eta \in T_x\mathcal M$;
--   2. (**Assumption 2.3**) for every $x \in \mathcal M$: $F(x,\cdot)$ and $\operatorname{grad}F(x,\cdot)$ are integrable, $\mathbb E_\xi F(x,\xi) = f(x)$, $\mathbb E_\xi\operatorname{grad}F(x,\xi) = \operatorname{grad}f(x)$ and $\mathbb E_\xi\|\operatorname{grad}F(x,\xi) - \operatorname{grad}f(x)\|^2 \le \sigma^2$.
--
--   Let $x^* \in \mathcal M$ minimize $f$ over $\mathcal M$, let $x_0 \in \mathcal M$, $\mu > 0$, and let the batch size satisfy $m \ge 16(d+4)$. Let $(x_k)_{k \ge 0}$ be the iterates of **ZO-RSGD** (Algorithm 2) with constant step $\eta_k = \hat\eta = 1/L$, driven by i.i.d. batches of $m$ independent pairs (standard Gaussian vector, noise sample). Then for every $N \in \mathbb N$
--
--   $$\frac{1}{N+1}\sum_{k=0}^{N}\mathbb E\,\|\operatorname{grad}f(x_k)\|^2 \le 4L\,\frac{f(x_0) - f(x^*)}{N+1} + C(\mu), \qquad C(\mu) = 2\mu^2L^2(d+6)^3 + \frac{16(d+4)}{m}\sigma^2 .$$
--
--   This is the non-asymptotic stationarity guarantee of zeroth-order Riemannian stochastic gradient descent: the average expected squared Riemannian gradient norm decays like $1/N$ up to a floor set by the smoothing parameter and the batch size.
--
--   **Formalization Note** The hypothesis $m \ge 16(d+4)$ is not in the theorem's statement on p. 17; the proof assumes it ("assuming that $m \ge 16(d+4)$"), and without it the absorption of the $\|\operatorname{grad}f\|^2$ term fails. The expectations are lower Lebesgue integrals against the product law of the i.i.d. batches (`pathLaw`), compared with `ENNReal.ofReal` of the right-hand side, so they cannot be junk values. The algorithm runs without a stopping index, so $x_{N+1}$ exists. Measurability of $(x,\eta) \mapsto R_x(\eta)$ and of $x \mapsto \operatorname{Proj}_{T_x\mathcal M}$ is assumed so that the iterates are random variables (true for closed $\mathcal M$ with a continuous retraction, e.g. spheres and Stiefel manifolds). The paper's "smooth" $f$ and $F(\cdot,\xi)$ are weakened to differentiable. $x^*$ is an attained minimizer of $f$ over $\mathcal M$. The step size $\hat\eta = 1/L$ appears as `1 / L`. The $O(\cdot)$ parameter choices (3.10) are not formalized.
-- source:
--   Li, Balasubramanian and Ma, arXiv:2003.11238v3, Theorem 3.2, (3.9), p. 17; Algorithm 2, p. 17; Assumption 2.3, p. 10

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ZORiem_RGD_IsRetraction
import Definitions.Def_ZORiem_RGD_rgrad
import Definitions.Def_ZORiem_RSGD_iterate

open MeasureTheory ProbabilityTheory ProjLikeRetr.Retractor
open scoped InnerProductSpace ENNReal

namespace ZORiem.RSGD

theorem theorem_3_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Set E) (d : ℕ) (hM : IsSubmanifold 1 d M)
    (R : E → E → E) (hR : ZORiem.RGD.IsRetraction M R) (hRmeas : Measurable (Function.uncurry R))
    (hPmeas : Measurable (fun x : E => (tangentSpace M x).starProjection))
    {Ξ : Type*} [MeasurableSpace Ξ] (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ]
    (F : E → Ξ → ℝ) (hFmeas : Measurable (Function.uncurry F))
    (f : E → ℝ) (hf : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
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
    (xstar : E) (hxstar : xstar ∈ M) (hmin : ∀ y ∈ M, f xstar ≤ f y)
    (x₀ : E) (hx₀ : x₀ ∈ M) (mu : ℝ) (hmu : 0 < mu)
    (m : ℕ) (hm : 16 * (d + 4) ≤ m) (N : ℕ) :
    (1 / ((N : ℝ≥0∞) + 1)) * ∑ k ∈ Finset.range (N + 1),
        ∫⁻ ω, ENNReal.ofReal (‖ZORiem.RGD.rgrad M f (iterate M R F mu (1 / L) m x₀ k ω)‖ ^ 2)
          ∂(pathLaw E Pξ m) ≤
      ENNReal.ofReal (4 * L * (f x₀ - f xstar) / ((N : ℝ) + 1) +
        (2 * mu ^ 2 * L ^ 2 * ((d : ℝ) + 6) ^ 3 + 16 * ((d : ℝ) + 4) / m * σ ^ 2)) := by sorry

end ZORiem.RSGD
