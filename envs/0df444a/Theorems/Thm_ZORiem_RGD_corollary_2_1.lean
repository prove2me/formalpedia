-- Prove2me | Theorems.Thm_ZORiem_RGD_corollary_2_1
-- name    : ZORiem.RGD.corollary_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:38.764702+00:00
-- url     : https://prove2.me/theorems/3bb28d9e-dda0-425d-8e03-0c31c8e0fe1e
-- title:
--   Corollary 2.1, p. 8 — E‖Pu₀‖^p ≤ (d+p)^{p/2} for the projection onto a d-dimensional subspace
-- statement:
--   Let $E$ be a finite-dimensional real inner product space (the ambient $\mathbb R^n$), let $\mathcal X\subseteq E$ be a linear subspace of dimension $d$ with orthogonal projection $P$, let $u_0\sim N(0,I_n)$ be a standard Gaussian vector of $E$ and $u=Pu_0$. For every real $p\ge2$, $\|u\|^p$ is integrable and
--
--   $$\mathbb E_{u_0}\|u\|^p\le(d+p)^{p/2}.$$
--
--   The point is that the bound depends on the dimension $d$ of the subspace, not on the ambient dimension $n$: for $\mathcal X=T_xM$ this replaces $n$ by the manifold dimension in all moment bounds of the paper, through the cases $p=3$ and $p=6$.
--
--   **Formalization Note** The paper states the corollary after Lemma 2.2, which is for integers $p\ge2$; here $p$ is any real number $p\ge2$ and $\|u\|^p$ is the real power, which only strengthens the statement. Finiteness of the moment is part of the conclusion.
-- source:
--   Li, Balasubramanian and Ma, arXiv:2003.11238v3, Corollary 2.1, p. 8

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ZORiem.RGD

/-- Corollary 2.1, p. 8: for `u₀ ∼ N(0, I_n)` and `u = P u₀`, with `P` the orthogonal projection
onto a `d`-dimensional subspace `X` of `E`, and every real `p ≥ 2`, the moment `E‖u‖^p` is finite
and `E‖u‖^p ≤ (d + p)^{p/2}`. -/
theorem corollary_2_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (X : Submodule ℝ E) (d : ℕ) (hd : Module.finrank ℝ X = d) (p : ℝ) (hp : 2 ≤ p) :
    Integrable (fun u₀ : E => ‖X.starProjection u₀‖ ^ p) (stdGaussian E) ∧
    ∫ u₀, ‖X.starProjection u₀‖ ^ p ∂(stdGaussian E) ≤ ((d : ℝ) + p) ^ (p / 2) := by sorry

end ZORiem.RGD
