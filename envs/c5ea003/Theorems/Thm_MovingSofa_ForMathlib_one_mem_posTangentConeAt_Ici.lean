-- Prove2me | Theorems.Thm_MovingSofa_ForMathlib_one_mem_posTangentConeAt_Ici
-- name    : MovingSofa.ForMathlib.one_mem_posTangentConeAt_Ici
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T15:15:31.396023+00:00
-- url     : https://prove2.me/theorems/fdc89a55-2cea-4aa1-b8d8-9dd0aa66d766
-- title:
--   Forward direction in the tangent cone of a right half-line
-- statement:
--   $1$ lies in the positive tangent cone of $[a,\infty)$ at $a$, via the segment $[a,a+1]$.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/Calculus/LocalExtr/OneSided.lean#L13-L15

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Linarith

namespace MovingSofa.ForMathlib

theorem one_mem_posTangentConeAt_Ici (a : ℝ) : (1 : ℝ) ∈ posTangentConeAt (Set.Ici a) a := by sorry

end MovingSofa.ForMathlib
