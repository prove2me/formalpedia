-- Prove2me | Theorems.Thm_YeIPA_MCP_residual_set_open_convex
-- name    : YeIPA.MCP.residual_set_open_convex
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:43.977511+00:00
-- url     : https://prove2.me/theorems/8a7b6b56-d117-4162-b649-77112a652fd1
-- title:
--   Theorem 8.23 — the residual set $R_{++}=\{s-f(x):(x,s)>0\}$ is open and convex
-- statement:
--   Let $f$ be a continuous monotone map from the open orthant $\mathbb R^n_{++}$ to $\mathbb R^n$, and let
--   $$R_{++}=\{s-f(x)\in\mathbb R^n: x>0,\ s>0\}$$
--   be the set of residuals of the monotone complementarity problem $s=f(x)$, $(x,s)\ge0$, $Xs=0$. Then $R_{++}$ is an open convex subset of $\mathbb R^n$.
--
--   Convexity of the residual set is what lets a homotopy path $s-f(x)=\theta r^0$, $\theta\in(0,1]$, connect a starting residual to points arbitrarily close to $0$; it is the "convex property" of §8.4.1 that the homogeneous model and its central path rely on.
--
--   **Formalization Note** The standing assumptions of §8.4.1 (continuity and monotonicity of $f$ on $\mathbb R^n_{++}$, p. 257) are explicit hypotheses. The book's proof rests on Theorem 8.19 (the map $(x,s)\mapsto(Xs,s-f(x))$ is a homeomorphism of $\mathbb R^{2n}_{++}$ onto $\mathbb R^n_{++}\times R_{++}$), whose proof is left as an exercise; it is not assumed here.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 259, Theorem 8.23

import Mathlib
import Definitions.Def_YeIPA_MCP_HomogeneousModel

open Matrix

namespace YeIPA.MCP

/-- Theorem 8.23 (Ye 1997, p. 259). Let `f` be a continuous monotone mapping from the open
orthant `ℝⁿ₊₊` to `ℝⁿ` (standing assumption of §8.4.1, p. 257). Then the residual set
`R₊₊ = {s − f(x) : (x, s) > 0}` is an open convex subset of `ℝⁿ`. -/
theorem residual_set_open_convex {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf_cont : ContinuousOn f (posOrthant n)) (hf_mono : MonotoneOnPos f) :
    IsOpen (Rpp f) ∧ Convex ℝ (Rpp f) := by sorry

end YeIPA.MCP
