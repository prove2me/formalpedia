-- Prove2me | Theorems.Thm_EuclideanSpace_volume_setOf_apply_mem_Icc
-- name    : EuclideanSpace.volume_setOf_apply_mem_Icc
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T16:13:34.255092+00:00
-- url     : https://prove2.me/theorems/6531650c-d9ca-4cc8-9df6-b745f7695b30
-- title:
--   Volume of a coordinate box
-- statement:
--   Closed coordinate boxes have product-of-lengths volume. Reduction to the coordinate map.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/MeasureTheory/EuclideanSpace.lean#L13-L24

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
open MeasureTheory

namespace EuclideanSpace

theorem volume_setOf_apply_mem_Icc (l r b t : ℝ) :
    volume {p : EuclideanSpace ℝ (Fin 2) | p 0 ∈ Set.Icc l r ∧ p 1 ∈ Set.Icc b t} =
      ENNReal.ofReal (r - l) * ENNReal.ofReal (t - b) := by sorry

end EuclideanSpace
