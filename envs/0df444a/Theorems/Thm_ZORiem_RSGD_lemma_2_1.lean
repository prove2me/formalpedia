-- Prove2me | Theorems.Thm_ZORiem_RSGD_lemma_2_1
-- name    : ZORiem.RSGD.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:43.093749+00:00
-- url     : https://prove2.me/theorems/692fa5b9-e506-482c-9854-727ec3b376ba
-- title:
--   Lemma 2.1, p. 8 — for x in a subspace 𝒳 and u = Pu₀, u₀ ∼ N(0, I): E⟨x, u⟩u = x and E⟨x, u⟩² = ‖x‖²
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, $\mathcal X \subseteq E$ a linear subspace of dimension $d$, and $P$ the orthogonal projection onto $\mathcal X$. Let $u_0$ be a standard Gaussian vector in $E$ and $u = Pu_0$. Then for every $x \in \mathcal X$ the maps $u_0 \mapsto \langle x, u\rangle u$ and $u_0 \mapsto \langle x, u\rangle^2$ are integrable and
--
--   $$\mathbb E_{u_0}\big[\langle x, u\rangle\,u\big] = x, \qquad \mathbb E_{u_0}\big[\langle x, u\rangle^2\big] = \|x\|^2 .$$
--
--   The projected Gaussian direction thus has identity covariance on $\mathcal X$; this is what makes the estimator $g_\mu$ approximately unbiased for the Riemannian gradient.
--
--   **Formalization Note** The paper writes the expectations as $\frac1\kappa\int_{\mathbb R^n}(\cdot)\,e^{-\|u_0\|^2/2}\,du_0$ with $\kappa = (2\pi)^{n/2}$; here they are integrals against Mathlib's `stdGaussian E`, which is that probability measure. Integrability is part of the conclusion, so the identities are not satisfied by a junk value of the Bochner integral.
-- source:
--   Li, Balasubramanian and Ma, arXiv:2003.11238v3, Lemma 2.1, (2.6), p. 8

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace ZORiem.RSGD

theorem lemma_2_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (X : Submodule ℝ E) (d : ℕ) (hX : Module.finrank ℝ X = d) (x : E) (hx : x ∈ X) :
    Integrable (fun u₀ : E => ⟪x, X.starProjection u₀⟫_ℝ • X.starProjection u₀)
        (stdGaussian E) ∧
      ∫ u₀, ⟪x, X.starProjection u₀⟫_ℝ • X.starProjection u₀ ∂(stdGaussian E) = x ∧
      Integrable (fun u₀ : E => ⟪x, X.starProjection u₀⟫_ℝ ^ 2) (stdGaussian E) ∧
      ∫ u₀, ⟪x, X.starProjection u₀⟫_ℝ ^ 2 ∂(stdGaussian E) = ‖x‖ ^ 2 := by sorry

end ZORiem.RSGD
