-- Prove2me | Theorems.Thm_ZORiem_RSGD_corollary_2_1
-- name    : ZORiem.RSGD.corollary_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:30.70545+00:00
-- url     : https://prove2.me/theorems/b10b79f0-c9b1-4d61-9f46-75973757b3d8
-- title:
--   Corollary 2.1, p. 8 — for u = Pu₀ with P the projection onto a d-dimensional subspace, E‖u‖^p ≤ (d + p)^{p/2}, p ≥ 2
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, $\mathcal X \subseteq E$ a linear subspace of dimension $d$, $P$ the orthogonal projection onto $\mathcal X$, and $u_0$ a standard Gaussian vector in $E$; put $u = Pu_0$. Then for every real $p \ge 2$ the function $u_0 \mapsto \|u\|^p$ is integrable and
--
--   $$\mathbb E_{u_0}\big(\|u\|^p\big) \le (d + p)^{p/2}.$$
--
--   The bound depends on the dimension $d$ of the subspace, not on the ambient dimension $n$; this is why the constants of the zeroth-order Riemannian method involve the manifold dimension only.
--
--   **Formalization Note** The paper states the corollary after Lemma 2.2, which is for integers $p \ge 2$; here $p$ is any real number $\ge 2$, which contains the integer case. $\|u\|^p$ is the real power `Real.rpow`.
-- source:
--   Li, Balasubramanian and Ma, arXiv:2003.11238v3, Corollary 2.1, p. 8

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ZORiem.RSGD

theorem corollary_2_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (X : Submodule ℝ E) (d : ℕ) (hX : Module.finrank ℝ X = d) (p : ℝ) (hp : 2 ≤ p) :
    Integrable (fun u₀ : E => ‖X.starProjection u₀‖ ^ p) (stdGaussian E) ∧
      ∫ u₀, ‖X.starProjection u₀‖ ^ p ∂(stdGaussian E) ≤ ((d : ℝ) + p) ^ (p / 2) := by sorry

end ZORiem.RSGD
