-- Prove2me | Theorems.Thm_YeIPA_MCP_slice_monotone_inequality
-- name    : YeIPA.MCP.slice_monotone_inequality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:38.097601+00:00
-- url     : https://prove2.me/theorems/c18bc914-095b-4f6d-812b-c147eead9b7f
-- title:
--   Lemma 8.20 — $(\theta^2-\theta^1)r^T(x^2-x^1)\le(x^2-x^1)^T(s^2-s^1)$ on the slices $S_{++}(\theta r)$
-- statement:
--   Let $f$ be a continuous monotone map from the open orthant $\mathbb R^n_{++}$ to $\mathbb R^n$, and for $r\in\mathbb R^n$ let $S_{++}(r)=\{(x,s)\in\mathbb R^{2n}_{++}: s=f(x)+r\}$. Fix $r\in\mathbb R^n$ and real numbers $\theta^1,\theta^2$. If $(x^1,s^1)\in S_{++}(\theta^1r)$ and $(x^2,s^2)\in S_{++}(\theta^2r)$, then
--   $$(\theta^2-\theta^1)\,r^T(x^2-x^1)\le(x^2-x^1)^T(s^2-s^1).$$
--
--   This inequality is the step from which the boundedness of the level sets (Lemma 8.21) and the convexity of the residual set (Theorem 8.23) follow.
--
--   **Formalization Note** Continuity and monotonicity of $f$ on $\mathbb R^n_{++}$ are the standing assumptions of §8.4.1 (p. 257) and are explicit hypotheses. The scalar multiple $\theta r$ is `θ • r`.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 258, Lemma 8.20

import Mathlib
import Definitions.Def_YeIPA_MCP_HomogeneousModel

open Matrix

namespace YeIPA.MCP

/-- Lemma 8.20 (Ye 1997, p. 258). Let `f` be continuous and monotone on the open orthant
`ℝⁿ₊₊` (standing assumption of §8.4.1, p. 257) and `r ∈ ℝⁿ`. If `(x¹, s¹) ∈ S₊₊(θ¹r)` and
`(x², s²) ∈ S₊₊(θ²r)` for real numbers `θ¹, θ²`, then
`(θ² − θ¹) rᵀ(x² − x¹) ≤ (x² − x¹)ᵀ(s² − s¹)`. -/
theorem slice_monotone_inequality {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf_cont : ContinuousOn f (posOrthant n)) (hf_mono : MonotoneOnPos f)
    (r : Fin n → ℝ) (θ₁ θ₂ : ℝ) (x₁ s₁ x₂ s₂ : Fin n → ℝ)
    (h₁ : (x₁, s₁) ∈ Spp f (θ₁ • r)) (h₂ : (x₂, s₂) ∈ Spp f (θ₂ • r)) :
    (θ₂ - θ₁) * (r ⬝ᵥ (x₂ - x₁)) ≤ (x₂ - x₁) ⬝ᵥ (s₂ - s₁) := by sorry

end YeIPA.MCP
