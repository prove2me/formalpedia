-- Prove2me | Theorems.Thm_MovingSofa_ForMathlib_neg_one_mem_posTangentConeAt_Iic
-- name    : MovingSofa.ForMathlib.neg_one_mem_posTangentConeAt_Iic
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T15:22:47.553373+00:00
-- url     : https://prove2.me/theorems/6915b28f-1ab8-47f3-b32b-fcefaed2e956
-- title:
--   Backward direction in the tangent cone of a left half-line
-- statement:
--   $-1$ lies in the positive tangent cone of $(-\infty,a]$ at $a$.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/Calculus/LocalExtr/OneSided.lean#L18-L21

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Linarith

namespace MovingSofa.ForMathlib

theorem neg_one_mem_posTangentConeAt_Iic (a : ℝ) :
    (-1 : ℝ) ∈ posTangentConeAt (Set.Iic a) a := by sorry

end MovingSofa.ForMathlib
