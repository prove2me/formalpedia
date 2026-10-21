-- Prove2me | Theorems.Thm_WrightPDIPM_Termination_lemma_A_4
-- name    : WrightPDIPM.Termination.lemma_A_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:15.888231+00:00
-- url     : https://prove2.me/theorems/2df18378-25ff-41f4-aa4c-3811cfa64978
-- title:
--   Lemma A.4 (Stewart–Todd) — χ(H) = sup over positive diagonal Σ of ‖ΣHᵀ(HΣHᵀ)⁻¹‖ is finite for full row rank H
-- statement:
--   Let $H \in \mathbb{R}^{p\times q}$ have full row rank $p$, and let $\mathcal D_+$ be the set of $q\times q$ diagonal matrices with strictly positive diagonal entries. Then
--   $$\chi(H) = \sup_{\Sigma\in\mathcal D_+} \bigl\|\Sigma H^{\mathsf T}(H\Sigma H^{\mathsf T})^{-1}\bigr\|$$
--   is finite, where $\|\cdot\|$ is the matrix norm induced by the Euclidean norm.
--
--   This bound, independent of the scaling $\Sigma$, is what makes weighted least-squares solutions bounded uniformly in the weights; it yields Lemma 7.2.
--
--   **Formalization Note** "$\chi(H)$ is finite" is stated as: there is $K$ with $\|\Sigma H^{\mathsf T}(H\Sigma H^{\mathsf T})^{-1}v\| \le K\|v\|$ for all $\Sigma = \operatorname{diag}(\sigma)$ with $\sigma > 0$ and all $v \in \mathbb{R}^p$, which is the induced-norm bound. Full row rank is `H.rank = p`; under it $H\Sigma H^{\mathsf T}$ is invertible, so Lean's matrix inverse is the true inverse.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 249, Lemma A.4

import Mathlib
import Definitions.Def_WrightPDIPM_Termination_Setup

namespace WrightPDIPM.Termination

open Matrix

/-- Lemma A.4 (Stewart–Todd, p. 249): if `H ∈ ℝ^{p×q}` has full row rank, then
`χ(H) = sup_{Σ ∈ D₊} ‖ΣHᵀ(HΣHᵀ)⁻¹‖` is finite, where `D₊` is the set of diagonal matrices with
strictly positive diagonal and `‖·‖` is the operator norm induced by the Euclidean norm: there
is `K` with `‖ΣHᵀ(HΣHᵀ)⁻¹v‖ ≤ K‖v‖` for all `Σ ∈ D₊` and all `v`. -/
theorem lemma_A_4 {p q : ℕ} (H : Matrix (Fin p) (Fin q) ℝ) (hH : H.rank = p) :
    ∃ K : ℝ, ∀ σ : Fin q → ℝ, (∀ j, 0 < σ j) → ∀ v : Fin p → ℝ,
      norm2 ((diagonal σ * Hᵀ * (H * diagonal σ * Hᵀ)⁻¹) *ᵥ v) ≤ K * norm2 v := by sorry

end WrightPDIPM.Termination
