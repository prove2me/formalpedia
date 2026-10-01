-- Prove2me | Theorems.Thm_MovingSofa_ForMathlib_hasDerivWithinAt_Ici_nonneg
-- name    : MovingSofa.ForMathlib.hasDerivWithinAt_Ici_nonneg
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T15:28:24.401659+00:00
-- url     : https://prove2.me/theorems/a67141b1-d61f-416f-be74-0356e2efdfa8
-- title:
--   Right derivative at a half-line minimum is nonnegative
-- statement:
--   A right derivative at a minimum over $[a,\infty)$ is $\ge0$ (Fermat, one-sided). Reduction to the tangent-cone helper.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/Calculus/LocalExtr/OneSided.lean#L24-L26

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Linarith

namespace MovingSofa.ForMathlib

theorem hasDerivWithinAt_Ici_nonneg {f : ℝ → ℝ} {f' a : ℝ}
    (h : IsLocalMinOn f (Set.Ici a) a) (hf : HasDerivWithinAt f f' (Set.Ici a) a) : 0 ≤ f' := by sorry

end MovingSofa.ForMathlib
