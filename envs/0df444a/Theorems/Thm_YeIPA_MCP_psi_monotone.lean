-- Prove2me | Theorems.Thm_YeIPA_MCP_psi_monotone
-- name    : YeIPA.MCP.psi_monotone
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:46.046978+00:00
-- url     : https://prove2.me/theorems/a3342571-aedf-4a74-baa1-8076c4cecfee
-- title:
--   Theorem 8.25 (ii) — if $f$ is continuous and monotone on $\mathbb R^n_{++}$, then $\psi$ is continuous and monotone on $\mathbb R^{n+1}_{++}$
-- statement:
--   Let $f$ be a continuous monotone map from the open orthant $\mathbb R^n_{++}$ to $\mathbb R^n$, i.e. $(x^1-x^2)^T(f(x^1)-f(x^2))\ge0$ for all $x^1,x^2>0$, and let $\psi(x,\tau)=(\tau f(x/\tau);\,-x^Tf(x/\tau))$ be given by (8.23). Then $\psi$ is a continuous monotone map from $\mathbb R^{n+1}_{++}$ to $\mathbb R^{n+1}$:
--   $$\big((x^1;\tau^1)-(x^2;\tau^2)\big)^T\big(\psi(x^1,\tau^1)-\psi(x^2,\tau^2)\big)\ge0\qquad\text{for all }(x^1;\tau^1),(x^2;\tau^2)>0.$$
--
--   Monotonicity of $\psi$ is what makes the homogeneous model (HMCP) a monotone complementarity problem again, so that interior-point methods for monotone problems apply to it.
--
--   **Formalization Note** No differentiability is assumed; the statement is about $\psi$ itself, not its Jacobian.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 261, Theorem 8.25 (ii)

import Mathlib
import Definitions.Def_YeIPA_MCP_HomogeneousModel

open Matrix

namespace YeIPA.MCP

/-- Theorem 8.25 (ii) (Ye 1997, p. 261). If `f` is a continuous monotone mapping from
`ℝⁿ₊₊` to `ℝⁿ`, then `ψ` of (8.23) is a continuous monotone mapping from `ℝⁿ⁺¹₊₊` to
`ℝⁿ⁺¹`. -/
theorem psi_monotone {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf_cont : ContinuousOn f (posOrthant n)) (hf_mono : MonotoneOnPos f) :
    ContinuousOn (psi f) (posOrthant (n + 1)) ∧ MonotoneOnPos (psi f) := by sorry

end YeIPA.MCP
