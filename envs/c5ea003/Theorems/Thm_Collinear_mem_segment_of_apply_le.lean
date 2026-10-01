-- Prove2me | Theorems.Thm_Collinear_mem_segment_of_apply_le
-- name    : Collinear.mem_segment_of_apply_le
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T17:32:08.151236+00:00
-- url     : https://prove2.me/theorems/a2064def-911c-4b4a-9d5a-6800d58fc621
-- title:
--   Separating functional puts a point in a segment
-- statement:
--   On a collinear set, a separating linear functional orders points into a segment via line parameter r>=1.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Convex/Collinear.lean#L26-L29

import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith
open Module

namespace Collinear

theorem mem_segment_of_apply_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (hs : Collinear ℝ s) {a p x : E}
    (ha : a ∈ s) (hp : p ∈ s) (hx : x ∈ s) (f : E →ₗ[ℝ] ℝ)
    (hpos : 0 < f (p - a)) (hle : f p ≤ f x) : p ∈ segment ℝ a x := by sorry

end Collinear
