-- Prove2me | Theorems.Thm_YeIPA_MCP_direction_inner_product
-- name    : YeIPA.MCP.direction_inner_product
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:53.897978+00:00
-- url     : https://prove2.me/theorems/fcf6b4da-fd9c-4247-b9cc-3b034bb9dc32
-- title:
--   Lemma 8.27 — $d_x^Td_s=d_x^T\nabla\psi(x^k)d_x+\eta(1-\eta-\gamma)(n+1)\mu^k$
-- statement:
--   Let $f$ be a continuous monotone map from $\mathbb R^n_{++}$ to $\mathbb R^n$, differentiable on $\mathbb R^n_{++}$, and let $\psi$ be the homogeneous map (8.23) on $\mathbb R^{n+1}_{++}$. Let $(x^k,s^k)>0$ be an iterate in $\mathbb R^{n+1}\times\mathbb R^{n+1}$, with residual $r^k=s^k-\psi(x^k)$ and $\mu^k=(x^k)^Ts^k/(n+1)$, let $\eta,\gamma\in(0,1)$, and let $(d_x,d_s)$ solve
--   $$d_s-\nabla\psi(x^k)d_x=-\eta r^k\quad(8.42),\qquad X^kd_s+S^kd_x=\gamma\mu^ke-X^ks^k\quad(8.43).$$
--   Then
--   $$d_x^Td_s=d_x^T\nabla\psi(x^k)d_x+\eta(1-\eta-\gamma)(n+1)\mu^k.$$
--
--   With $\gamma=1-\eta$ the last term vanishes, so $d_x^Td_s\ge0$ by monotonicity; this is the identity behind the step analysis of Theorem 8.29.
--
--   **Formalization Note** $\nabla\psi$ is Mathlib's `fderiv` of `psi f`; $\mu^k$ is `mu x s`. The standing assumptions of §8.4 (continuity, monotonicity and differentiability of $f$ on $\mathbb R^n_{++}$) and the book's "$\eta$ and $\gamma$ are proper given parameters between 0 and 1" (p. 268) are explicit hypotheses. Any solution $(d_x,d_s)$ of (8.42)–(8.43) is allowed.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 268, Lemma 8.27

import Mathlib
import Definitions.Def_YeIPA_MCP_HomogeneousModel

open Matrix

namespace YeIPA.MCP

/-- Lemma 8.27 (Ye 1997, p. 268). Let `f` be continuous, monotone and differentiable on
`ℝⁿ₊₊` (standing assumptions of §8.4), let `(xᵏ, sᵏ) > 0` in `ℝⁿ⁺¹`, let `η, γ ∈ (0, 1)`,
and let `(d_x, d_s)` solve (8.42)–(8.43). Then
`d_xᵀd_s = d_xᵀ∇ψ(xᵏ)d_x + η(1 − η − γ)(n + 1)μᵏ`, `μᵏ = (xᵏ)ᵀsᵏ/(n + 1)`. -/
theorem direction_inner_product {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf_cont : ContinuousOn f (posOrthant n)) (hf_mono : MonotoneOnPos f)
    (hf_diff : DifferentiableOn ℝ f (posOrthant n))
    (η γ : ℝ) (hη₀ : 0 < η) (hη₁ : η < 1) (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (x s dx ds : Fin (n + 1) → ℝ) (hx : x ∈ posOrthant (n + 1)) (hs : s ∈ posOrthant (n + 1))
    (hdir : IsDirection f η γ x s dx ds) :
    dx ⬝ᵥ ds =
      dx ⬝ᵥ fderiv ℝ (psi f) x dx + η * (1 - η - γ) * ((n : ℝ) + 1) * mu x s := by sorry

end YeIPA.MCP
