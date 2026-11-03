-- Prove2me | Theorems.Thm_ZeroOneIALM_isCoercive_isBoundedBelow
-- name    : ZeroOneIALM.isCoercive_isBoundedBelow
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:28:39.67197+00:00
-- url     : https://prove2.me/theorems/77254b13-6d79-4c80-b42a-c4b5647d8ccd
-- title:
--   Assumption 4 implies Assumption 3: a continuous coercive function is bounded below
-- statement:
--   Let $f:\mathbb R^p\to\mathbb R$ be continuous and coercive. Then $f$ is bounded below.
--
--   The paper states this for the smooth function $f$: Assumption 4 is stronger than Assumption 3, so the results stated under boundedness below remain available under coercivity.
--
--   Differences from the source:
--   - generalization: the smooth function f → a continuous function f; reason: a smooth function is continuous
-- source:
--   Zhang & Xiu, Global Convergence of Inexact Augmented Lagrangian Method for Zero-One Composite Optimization, arXiv:2112.00440v1, p.22, sentence following Assumption 4

import Mathlib
import Definitions.Def_ZeroOneIALM_Assumptions

namespace ZeroOneIALM

/-- Assumption 4 is stronger than Assumption 3 for smooth `f`, Zhang & Xiu, arXiv:2112.00440v1,
p.22: a continuous coercive function on `ℝᵖ` is bounded below. -/
theorem isCoercive_isBoundedBelow {p : ℕ} {f : EuclideanSpace ℝ (Fin p) → ℝ}
    (hcont : Continuous f) (hf : IsCoercive f) : IsBoundedBelow f := by sorry

end ZeroOneIALM
