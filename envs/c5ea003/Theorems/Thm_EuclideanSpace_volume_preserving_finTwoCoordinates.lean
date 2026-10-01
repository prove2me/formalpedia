-- Prove2me | Theorems.Thm_EuclideanSpace_volume_preserving_finTwoCoordinates
-- name    : EuclideanSpace.volume_preserving_finTwoCoordinates
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T16:04:18.264105+00:00
-- url     : https://prove2.me/theorems/e05b400d-ba13-4093-8128-0c157366e824
-- title:
--   Coordinate map preserves volume
-- statement:
--   Coordinate pairing is volume preserving via finTwoArrow and toLp.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/MeasureTheory/EuclideanSpace.lean#L7-L10

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
open MeasureTheory

namespace EuclideanSpace

theorem volume_preserving_finTwoCoordinates :
    MeasurePreserving (fun p : EuclideanSpace ℝ (Fin 2) ↦ (p 0, p 1)) volume volume := by sorry

end EuclideanSpace
