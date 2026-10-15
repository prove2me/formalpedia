-- Prove2me | Theorems.Thm_ZORiem_RGD_lemma_2_1
-- name    : ZORiem.RGD.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:38.887785+00:00
-- url     : https://prove2.me/theorems/51f1f2de-77b7-4d30-9643-31fe6f514f12
-- title:
--   Lemma 2.1, p. 8 — E[⟨x,u⟩u] = x and E⟨x,u⟩² = ‖x‖² for u the projection of a standard Gaussian onto a subspace containing x
-- statement:
--   Let $E$ be a finite-dimensional real inner product space (the ambient $\mathbb R^n$), let $\mathcal X\subseteq E$ be a linear subspace of dimension $d$ with orthogonal projection $P$, let $u_0\sim N(0,I_n)$ be a standard Gaussian vector of $E$ and $u=Pu_0$. Then for every $x\in\mathcal X$ the random vector $\langle x,u\rangle u$ is integrable and
--
--   $$\mathbb E_{u_0}\big[\langle x,u\rangle\,u\big]=x,\qquad \mathbb E_{u_0}\big[\langle x,u\rangle^2\big]=\|x\|^2 .$$
--
--   In the paper both expectations are written as integrals against the Gaussian density $\kappa^{-1}e^{-\|u_0\|^2/2}$, $\kappa=(2\pi)^{n/2}$. Applied with $\mathcal X=T_xM$ and $x=\operatorname{grad}f(x)$, the identities say that the projected Gaussian direction is isotropic on the tangent space, which is the basis of every bias estimate for the estimator $g_\mu$.
--
--   **Formalization Note** The standard Gaussian is Mathlib's `stdGaussian E`, so $\kappa^{-1}\int\cdots e^{-\|u_0\|^2/2}du_0$ is the integral against it. The dimension hypothesis $\dim\mathcal X=d$ is the page's "$d$-dimensional" and is not needed for the conclusion.
-- source:
--   Li, Balasubramanian and Ma, arXiv:2003.11238v3, Lemma 2.1, (2.6), p. 8

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace ZORiem.RGD

/-- Lemma 2.1, p. 8: for a `d`-dimensional subspace `X` of `E` with orthogonal projection `P`, a
standard Gaussian `u₀ ∼ N(0, I_n)` and `u = P u₀`, every `x ∈ X` satisfies `E[⟨x, u⟩ u] = x` and
`E[⟨x, u⟩²] = ‖x‖²` (the vector-valued integrand is integrable). -/
theorem lemma_2_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (X : Submodule ℝ E) (d : ℕ) (hd : Module.finrank ℝ X = d) (x : E) (hx : x ∈ X) :
    Integrable (fun u₀ : E => ⟪x, X.starProjection u₀⟫_ℝ • X.starProjection u₀) (stdGaussian E) ∧
    ∫ u₀, ⟪x, X.starProjection u₀⟫_ℝ • X.starProjection u₀ ∂(stdGaussian E) = x ∧
    ∫ u₀, ⟪x, X.starProjection u₀⟫_ℝ ^ 2 ∂(stdGaussian E) = ‖x‖ ^ 2 := by sorry

end ZORiem.RGD
