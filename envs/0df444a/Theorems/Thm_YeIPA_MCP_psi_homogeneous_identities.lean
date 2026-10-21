-- Prove2me | Theorems.Thm_YeIPA_MCP_psi_homogeneous_identities
-- name    : YeIPA.MCP.psi_homogeneous_identities
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:52.389134+00:00
-- url     : https://prove2.me/theorems/b9fd2c3f-4ed5-4bfb-9779-9223c3370e67
-- title:
--   Theorem 8.25 (i) — $\psi$ is continuous and homogeneous of degree 1, $(x;\tau)^T\psi(x,\tau)=0$ and $(x;\tau)^T\nabla\psi(x,\tau)=-\psi(x,\tau)^T$
-- statement:
--   Let $f$ be a continuous monotone map from $\mathbb R^n_{++}$ to $\mathbb R^n$ that is differentiable on $\mathbb R^n_{++}$, and let $\psi(x,\tau)=(\tau f(x/\tau);\,-x^Tf(x/\tau))$ be given by (8.23). Then:
--
--   1. $\psi$ is continuous on $\mathbb R^{n+1}_{++}$ and homogeneous of degree $1$: $\psi(t(x;\tau))=t\,\psi(x;\tau)$ for all $(x;\tau)>0$ and $t>0$;
--   2. for every $(x;\tau)\in\mathbb R^{n+1}_{++}$,
--   $$(x;\tau)^T\psi(x,\tau)=0\qquad\text{and}\qquad(x;\tau)^T\nabla\psi(x,\tau)=-\psi(x,\tau)^T.$$
--
--   These identities, written (8.41) in §8.4.4, drive the algebra of the interior-point step: the complementarity gap of the homogeneous model equals the inner product of the iterate with its residual.
--
--   **Formalization Note** The row-vector identity $(x;\tau)^T\nabla\psi(x,\tau)=-\psi(x,\tau)^T$ is stated by applying both sides to an arbitrary $d\in\mathbb R^{n+1}$: $z^T(\nabla\psi(z)d)=-\psi(z)^Td$. $\nabla\psi$ is Mathlib's `fderiv`. Continuity and monotonicity of $f$ are the standing assumptions of §8.4.1 (p. 257); differentiability on $\mathbb R^n_{++}$ is the section's silent assumption behind $\nabla\psi$. Homogeneity is required for positive scalars, the ones that keep the point in $\mathbb R^{n+1}_{++}$.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 260, Theorem 8.25 (i)

import Mathlib
import Definitions.Def_YeIPA_MCP_HomogeneousModel

open Matrix

namespace YeIPA.MCP

/-- Theorem 8.25 (i) (Ye 1997, p. 260). Let `f` be continuous and monotone on `ℝⁿ₊₊`
(standing assumption of §8.4.1, p. 257) and differentiable there (so that `∇ψ` exists), and let
`ψ` be given by (8.23). Then `ψ` is a continuous homogeneous function of degree 1 on
`ℝⁿ⁺¹₊₊`, and for every `(x; τ) ∈ ℝⁿ⁺¹₊₊`, `(x; τ)ᵀψ(x, τ) = 0` and
`(x; τ)ᵀ∇ψ(x, τ) = −ψ(x, τ)ᵀ` (the last as an identity of linear forms in `d ∈ ℝⁿ⁺¹`). -/
theorem psi_homogeneous_identities {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf_cont : ContinuousOn f (posOrthant n)) (hf_mono : MonotoneOnPos f)
    (hf_diff : DifferentiableOn ℝ f (posOrthant n)) :
    ContinuousOn (psi f) (posOrthant (n + 1)) ∧
    (∀ z ∈ posOrthant (n + 1), ∀ t : ℝ, 0 < t → psi f (t • z) = t • psi f z) ∧
    (∀ z ∈ posOrthant (n + 1), z ⬝ᵥ psi f z = 0) ∧
    (∀ z ∈ posOrthant (n + 1), ∀ d : Fin (n + 1) → ℝ,
      z ⬝ᵥ fderiv ℝ (psi f) z d = -(psi f z ⬝ᵥ d)) := by sorry

end YeIPA.MCP
