-- Prove2me | Theorems.Thm_MovingSofa_ForMathlib_isLinearMap_inner_left
-- name    : MovingSofa.ForMathlib.isLinearMap_inner_left
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-29T21:48:44.777523+00:00
-- url     : https://prove2.me/theorems/c241898c-c8f9-4838-af81-8b46a34c643c
-- title:
--   Linearity of the real inner product in its left slot
-- statement:
--   Let $E$ be a real inner product space and $v\in E$ fixed. Then the map $x\mapsto\langle x,v\rangle$ is linear over $\mathbb{R}$. In symbols $$x\mapsto\langle x,v\rangle\quad\text{is }\mathbb{R}\text{-linear}.$$ This packages the left slot for the half-space convexity lemmas.\n\n**Formalization Note** Wrapped in `MovingSofa.ForMathlib` to avoid collision with the short top-level name in the source; statement otherwise verbatim.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/InnerProductSpace/Linear.lean#L12-L14

import Mathlib.Analysis.InnerProductSpace.Basic
open InnerProductSpace

namespace MovingSofa.ForMathlib

theorem isLinearMap_inner_left {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : E) : IsLinearMap ℝ fun x : E ↦ inner ℝ x v := by sorry

end MovingSofa.ForMathlib
