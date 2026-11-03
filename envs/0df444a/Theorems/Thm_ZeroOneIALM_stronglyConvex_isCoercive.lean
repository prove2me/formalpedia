-- Prove2me | Theorems.Thm_ZeroOneIALM_stronglyConvex_isCoercive
-- name    : ZeroOneIALM.stronglyConvex_isCoercive
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:28:41.203823+00:00
-- url     : https://prove2.me/theorems/996db992-ea68-4be8-800a-7fcc5d11b34a
-- title:
--   Assumption 5 implies Assumption 4: a strongly convex function on $\mathbb R^p$ is coercive
-- statement:
--   Let $f:\mathbb R^p\to\mathbb R$ be strongly convex, with some positive modulus. Then $f$ is coercive:
--   $$
--   \lim_{\|w\|\to\infty}f(w)=\infty.
--   $$
--
--   The paper states that Assumption 5 is stronger than Assumption 4, which lets the results stated under coercivity be used in the proof of Theorem 7.
--
--   Differences from the source:
--   - generalization: f smooth, as throughout the paper → no smoothness of f; reason: the printed claim is the instance with smooth f
-- source:
--   Zhang & Xiu, Global Convergence of Inexact Augmented Lagrangian Method for Zero-One Composite Optimization, arXiv:2112.00440v1, p.25, sentence preceding Assumption 5

import Mathlib
import Definitions.Def_ZeroOneIALM_Assumptions

namespace ZeroOneIALM

/-- Assumption 5 is stronger than Assumption 4, Zhang & Xiu, arXiv:2112.00440v1, p.25: a strongly
convex function on `ℝᵖ` is coercive. -/
theorem stronglyConvex_isCoercive {p : ℕ} {f : EuclideanSpace ℝ (Fin p) → ℝ}
    (hf : IsStronglyConvex f) : IsCoercive f := by sorry

end ZeroOneIALM
