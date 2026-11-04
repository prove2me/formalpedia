-- Prove2me | Theorems.Thm_MovingSofa_ForMathlib_hasDerivAt_if_le
-- name    : MovingSofa.ForMathlib.hasDerivAt_if_le
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-11-04T02:56:08.149197+00:00
-- url     : https://prove2.me/theorems/e1c5e693-0d1b-4b3e-851c-1c2ea911d561
-- title:
--   Glueing derivatives along a threshold
-- statement:
--   Two everywhere-differentiable functions agreeing in value and derivative at a threshold glue to a differentiable function with glued derivative.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/Calculus/Interval.lean#L36-L62

import Mathlib.Analysis.Calculus.ContDiff.Deriv
open Set

namespace MovingSofa.ForMathlib

theorem hasDerivAt_if_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g f' g' : ℝ → E} {c : ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hfg : f c = g c) (hfg' : f' c = g' c) (t : ℝ) :
    HasDerivAt (fun s => if s ≤ c then f s else g s) (if t ≤ c then f' t else g' t) t := by sorry

end MovingSofa.ForMathlib
