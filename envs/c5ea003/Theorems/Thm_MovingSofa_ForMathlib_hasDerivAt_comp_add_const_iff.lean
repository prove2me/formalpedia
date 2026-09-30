-- Prove2me | Theorems.Thm_MovingSofa_ForMathlib_hasDerivAt_comp_add_const_iff
-- name    : MovingSofa.ForMathlib.hasDerivAt_comp_add_const_iff
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-29T22:02:18.797874+00:00
-- url     : https://prove2.me/theorems/dd601a4e-2631-4c57-a6a4-9557eb81952e
-- title:
--   Derivative at a shifted base point, both directions
-- statement:
--   Let $f:\mathbb{K}\to F$ with derivative $f'$ ($\mathbb{K}$ a nontrivially normed field). For shift $a$ and base $x$, $$\mathrm{HasDerivAt}(u\mapsto f(u+a),f',x)\iff\mathrm{HasDerivAt}(f,f',x+a).$$ The forward direction shifts back by $-a$; the converse is Mathlib's `comp_add_const`.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/Calculus/Deriv/Shift.lean#L11-L13

import Mathlib.Analysis.Calculus.Deriv.Shift

namespace MovingSofa.ForMathlib

theorem hasDerivAt_comp_add_const_iff {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F} {f' : F} (x a : 𝕜) : HasDerivAt (fun u ↦ f (u + a)) f' x ↔ HasDerivAt f f' (x + a) := by sorry

end MovingSofa.ForMathlib
