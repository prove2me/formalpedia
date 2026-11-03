-- Prove2me | Theorems.Thm_ZeroOneIALM_pStationaryTriplet_finite
-- name    : ZeroOneIALM.pStationaryTriplet_finite
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:30:49.756478+00:00
-- url     : https://prove2.me/theorems/3735ab2d-c34f-494d-b46d-1a492a675f99
-- title:
--   Proof of Theorem 7: problem (2) has finitely many P-stationary triplets
-- statement:
--   Let $f:\mathbb R^p\to\mathbb R$ be differentiable and strongly convex, let $\lambda>0$, and let $A$ have full row rank. Then the set of P-stationary triplets $(w;u;z)$ of problem (2), over all constants $\alpha>0$ of Definition 2, is finite.
--
--   The paper proves this as the first step of Theorem 7. Finiteness makes every accumulation point of the iteration isolated, which is the hypothesis of the convergence result of Kanzow and Qi.
--
--   Differences from the source:
--   - generalization: under Assumptions 1, 2 and 5, inside the proof of Theorem 7 → f differentiable and strongly convex, with no Lipschitz bound on the gradient; reason: the argument uses no Lipschitz bound, and the printed claim is the instance with Assumption 1
--   - generalization: Assumption 2 with γ := √θ_min(AAᵀ) > 0 → any γ > 0 with γ‖z‖ ≤ ‖Aᵀz‖ for every z; reason: the paper’s γ satisfies this inequality, so the printed statement is the instance γ = √θ_min(AAᵀ), and the proof uses Assumption 2 only through this inequality
--   - encoding: A ∈ ℝⁿˣᵖ and its transpose Aᵀ → a continuous linear map between Euclidean spaces and its adjoint; reason: the same objects in the standard bases
-- source:
--   Zhang & Xiu, Global Convergence of Inexact Augmented Lagrangian Method for Zero-One Composite Optimization, arXiv:2112.00440v1, proof of Theorem 7, pp.25–26, "the number of P-stationary triplet of (2) is finite"

import Mathlib
import Definitions.Def_ZeroOneIALM_Assumptions
import Definitions.Def_ZeroOneIALM_PStationary

namespace ZeroOneIALM

/-- The first step of the proof of Theorem 7, Zhang & Xiu, arXiv:2112.00440v1, pp.25–26: for
differentiable strongly convex `f`, `λ > 0` and `A` of full row rank, the set of P-stationary
triplets of problem (2) is finite. The triplets are those of Definition 2, for any constant
`α > 0`. -/
theorem pStationaryTriplet_finite {p n : ℕ} {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {b : EuclideanSpace ℝ (Fin n)} {lam γ : ℝ}
    (hlam : 0 < lam) (hdiff : Differentiable ℝ f) (hconv : IsStronglyConvex f)
    (h2 : IsRowRankConstant A γ) :
    {t : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
      IsPStationaryTriplet f A b lam t.1 t.2.1 t.2.2}.Finite := by sorry

end ZeroOneIALM
