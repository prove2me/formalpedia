-- Prove2me | Theorems.Thm_MovingSofa_ForMathlib_exists_first_return
-- name    : MovingSofa.ForMathlib.exists_first_return
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T18:18:01.993+00:00
-- url     : https://prove2.me/theorems/9404e869-ad90-47b9-b7d2-93a318ad7667
-- title:
--   First return to a level exists
-- statement:
--   A continuous function starting below a level and reaching it has a first hitting time via sInf of the superlevel set.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/Calculus/FirstReturn.lean#L13-L15

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

namespace MovingSofa.ForMathlib

theorem exists_first_return {g : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (hcont : ContinuousOn g (Set.Icc a b)) (hga : g a < c) (hgb : c ≤ g b) :
    ∃ t ∈ Set.Ioc a b, g t = c ∧ ∀ u ∈ Set.Ico a t, g u < c := by sorry

end MovingSofa.ForMathlib
