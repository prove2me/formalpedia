-- Prove2me | Theorems.Thm_EuclideanSpace_volume_preserving_finTwoCoordinatesSwap
-- name    : EuclideanSpace.volume_preserving_finTwoCoordinatesSwap
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T16:13:52.992875+00:00
-- url     : https://prove2.me/theorems/9f776b50-bd5a-4536-8233-77e3dfdaf2ef
-- title:
--   Swapped coordinates preserve volume
-- statement:
--   Reading coordinates second-first preserves volume. Reduction.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/MeasureTheory/EuclideanSpace.lean#L31-L40

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_MovingSofa_ForMathlib_EuclideanSpace
open MeasureTheory
open EuclideanSpace

namespace EuclideanSpace

theorem volume_preserving_finTwoCoordinatesSwap :
    MeasurePreserving finTwoCoordinatesSwap volume
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by sorry

end EuclideanSpace
