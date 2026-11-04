-- Prove2me | Theorems.Thm_MovingSofa_ForMathlib_contDiff_one_of_hasDerivAt
-- name    : MovingSofa.ForMathlib.contDiff_one_of_hasDerivAt
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-11-04T02:57:15.687654+00:00
-- url     : https://prove2.me/theorems/2d0779aa-ce3a-46ff-beb6-a1511170dc8a
-- title:
--   Global derivative field gives differentiability
-- statement:
--   A globally defined continuous derivative field witnesses continuous differentiability.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/Calculus/Interval.lean#L65-L68

import Mathlib.Analysis.Calculus.ContDiff.Deriv
open Set

namespace MovingSofa.ForMathlib

theorem contDiff_one_of_hasDerivAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f') :
    ContDiff ℝ 1 f := by sorry

end MovingSofa.ForMathlib
