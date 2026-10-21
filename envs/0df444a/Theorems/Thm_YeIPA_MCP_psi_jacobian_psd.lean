-- Prove2me | Theorems.Thm_YeIPA_MCP_psi_jacobian_psd
-- name    : YeIPA.MCP.psi_jacobian_psd
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:42.984984+00:00
-- url     : https://prove2.me/theorems/cd7fb8d3-951c-40c0-808d-4f45e9d0b096
-- title:
--   Lemma 8.24 — if $\nabla f$ is positive semi-definite on $\mathbb R^n_{++}$, then so is $\nabla\psi$ on $\mathbb R^{n+1}_{++}$
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R^n$ be differentiable on the open orthant $\mathbb R^n_{++}$ with positive semi-definite Jacobian there, i.e. $d^T\nabla f(x)d\ge0$ for every $x>0$ and $d\in\mathbb R^n$ ($\nabla f(x)$ need not be symmetric). Let $\psi(x,\tau)=(\tau f(x/\tau);\,-x^Tf(x/\tau))$ be the homogeneous map (8.23) on $\mathbb R^{n+1}_{++}$. Then $\nabla\psi$ is positive semi-definite on $\mathbb R^{n+1}_{++}$: for every $(x;\tau)>0$,
--   $$(d_x;d_\tau)^T\,\nabla\psi(x,\tau)\,(d_x;d_\tau)\ge0\qquad\text{for all }(d_x;d_\tau)\in\mathbb R^{n+1}.$$
--
--   This is the infinitesimal form of the monotonicity of $\psi$; the interior-point analysis of §8.4.4 uses it as $d_x^T\nabla\psi(x^k)d_x\ge0$.
--
--   **Formalization Note** $\nabla\psi(x,\tau)$ is the Jacobian of $\psi$ (Mathlib's `fderiv`), and the quadratic form is `d ⬝ᵥ fderiv ℝ (psi f) z d`. The book also displays this Jacobian as the block matrix (8.24); the lower-left block printed there, $-f(x/\tau)^T-(x/\tau)^T\nabla f(x/\tau)^T$, has a spurious transpose (the Jacobian's block is $-f(x/\tau)^T-(x/\tau)^T\nabla f(x/\tau)$), and with the printed block the lemma fails for nonsymmetric $\nabla f$; the statement here is about the true Jacobian, which is what the proof (8.25) computes. Differentiability of $f$ on $\mathbb R^n_{++}$ is the section's silent assumption behind $\nabla f$, made explicit.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 260, Lemma 8.24

import Mathlib
import Definitions.Def_YeIPA_MCP_HomogeneousModel

open Matrix

namespace YeIPA.MCP

/-- Lemma 8.24 (Ye 1997, p. 260). Let `f` be differentiable on the open orthant `ℝⁿ₊₊` with
`∇f` positive semi-definite there (`dᵀ∇f(x)d ≥ 0` for all `x > 0`, `d ∈ ℝⁿ`). Then `∇ψ` is
positive semi-definite on `ℝⁿ⁺¹₊₊`: for every `(x; τ) > 0` and every `(d_x; d_τ) ∈ ℝⁿ⁺¹`,
`(d_x; d_τ)ᵀ ∇ψ(x, τ) (d_x; d_τ) ≥ 0`, where `ψ` is (8.23) and `∇ψ` is its Jacobian. -/
theorem psi_jacobian_psd {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf_diff : DifferentiableOn ℝ f (posOrthant n))
    (hf_psd : ∀ x ∈ posOrthant n, ∀ d : Fin n → ℝ, 0 ≤ d ⬝ᵥ fderiv ℝ f x d) :
    ∀ z ∈ posOrthant (n + 1), ∀ d : Fin (n + 1) → ℝ, 0 ≤ d ⬝ᵥ fderiv ℝ (psi f) z d := by sorry

end YeIPA.MCP
