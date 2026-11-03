-- Prove2me | Theorems.Thm_ZeroOneIALM_lemma_3_ii
-- name    : ZeroOneIALM.lemma_3_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:30:45.258224+00:00
-- url     : https://prove2.me/theorems/525178f4-f114-4425-a38e-9046a9e7222a
-- title:
--   Lemma 3 (ii): for convex $f$, a P-stationary point is a local minimizer
-- statement:
--   Let $f:\mathbb R^p\to\mathbb R$ be convex and differentiable and let $\lambda>0$. If $(w^*;u^*)$ is a P-stationary point of problem (2), with some constant $\alpha>0$, then $(w^*;u^*)$ is a local minimizer of (2).
--
--   This is the last step of the proof of Theorem 7, identifying the limit of the algorithm as a local minimizer. The result is due to Zhou et al.
--
--   Differences from the source:
--   - generalization: f smooth, as in (2) → f differentiable; reason: the printed claim is the instance with smooth f
--   - encoding: A ∈ ℝⁿˣᵖ and its transpose Aᵀ → a continuous linear map between Euclidean spaces and its adjoint; reason: the same objects in the standard bases
--   - encoding: local minimizer of (2), a notion the paper does not spell out → feasible, with least objective among feasible pairs satisfying ‖w − w*‖² + ‖u − u*‖² < δ²; reason: the standard notion for a constrained problem, with the Euclidean ball of p.4
-- source:
--   Zhang & Xiu, Global Convergence of Inexact Augmented Lagrangian Method for Zero-One Composite Optimization, arXiv:2112.00440v1, Lemma 3 (ii), p.11, citing Zhou et al. [44, Theorem 3.3]

import Mathlib
import Definitions.Def_ZeroOneIALM_LocalMinimizer
import Definitions.Def_ZeroOneIALM_PStationary

namespace ZeroOneIALM

/-- Lemma 3 (ii) (Zhou et al., Theorem 3.3), Zhang & Xiu, arXiv:2112.00440v1, p.11: if `f` is a
convex function, then a P-stationary point of problem (2), with some constant `α > 0`, is a local
minimizer of (2). -/
theorem lemma_3_ii {p n : ℕ} {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {b : EuclideanSpace ℝ (Fin n)} {lam : ℝ}
    (hlam : 0 < lam) (hdiff : Differentiable ℝ f) (hconv : ConvexOn ℝ Set.univ f)
    {wstar : EuclideanSpace ℝ (Fin p)} {ustar : EuclideanSpace ℝ (Fin n)}
    (hstat : IsPStationaryPoint f A b lam wstar ustar) :
    IsLocalMinimizer f A b lam wstar ustar := by sorry

end ZeroOneIALM
