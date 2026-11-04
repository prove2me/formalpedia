-- Prove2me | Theorems.Thm_MovingSofa_ForMathlib_contDiffOn_one_of_continuous_derivative
-- name    : MovingSofa.ForMathlib.contDiffOn_one_of_continuous_derivative
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-11-04T02:54:53.502554+00:00
-- url     : https://prove2.me/theorems/19acb034-530f-41c3-8400-ade035beba0b
-- title:
--   Continuous derivative field gives order-one regularity
-- statement:
--   A continuous derivative field on a uniquely differentiable set gives order-one regularity via the derivative-within characterization.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/Calculus/Interval.lean#L21-L30

import Mathlib.Analysis.Calculus.ContDiff.Deriv
open Set

namespace MovingSofa.ForMathlib

theorem contDiffOn_one_of_continuous_derivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (f : ℝ → E) (d : s → E) (hd : Continuous d)
    (hf : ∀ t : s, HasDerivWithinAt f (d t) s t) : ContDiffOn ℝ 1 f s := by sorry

end MovingSofa.ForMathlib
