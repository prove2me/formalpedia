-- Prove2me | Theorems.Thm_MovingSofa_ForMathlib_nonneg_of_first_return
-- name    : MovingSofa.ForMathlib.nonneg_of_first_return
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T18:23:46.542988+00:00
-- url     : https://prove2.me/theorems/a8d2eb42-4c25-469b-8fe2-d07d4e4e35f1
-- title:
--   Derivative at a first return is nonnegative
-- statement:
--   At a first return from below, the derivative is nonnegative via left slopes.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/Calculus/FirstReturn.lean#L40-L42

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

namespace MovingSofa.ForMathlib

theorem nonneg_of_first_return {g : ℝ → ℝ} {a t c d : ℝ} (hat : a < t)
    (hd : HasDerivAt g d t) (hgt : g t = c) (hleft : ∀ u ∈ Set.Ico a t, g u < c) :
    0 ≤ d := by sorry

end MovingSofa.ForMathlib
