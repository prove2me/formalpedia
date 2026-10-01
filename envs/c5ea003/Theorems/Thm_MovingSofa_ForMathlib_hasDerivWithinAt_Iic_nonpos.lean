-- Prove2me | Theorems.Thm_MovingSofa_ForMathlib_hasDerivWithinAt_Iic_nonpos
-- name    : MovingSofa.ForMathlib.hasDerivWithinAt_Iic_nonpos
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T15:28:35.958217+00:00
-- url     : https://prove2.me/theorems/feeb8603-23c3-49ca-9d79-1d322e7a5ab0
-- title:
--   Left derivative at a half-line minimum is nonpositive
-- statement:
--   A left derivative at a minimum over $(-\infty,a]$ is $\le0$. Reduction to the helper.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/Calculus/LocalExtr/OneSided.lean#L29-L32

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Linarith

namespace MovingSofa.ForMathlib

theorem hasDerivWithinAt_Iic_nonpos {f : ℝ → ℝ} {f' a : ℝ}
    (h : IsLocalMinOn f (Set.Iic a) a) (hf : HasDerivWithinAt f f' (Set.Iic a) a) : f' ≤ 0 := by sorry

end MovingSofa.ForMathlib
