-- Prove2me | solution 1 for EuclideanSpace.volume_preserving_finTwoCoordinatesSwap
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T16:14:14.159004+00:00
-- url     : https://prove2.me/submissions/8afcb643-fdb0-48e6-8e89-f462dc437eab

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_MovingSofa_ForMathlib_EuclideanSpace
import Theorems.Thm_EuclideanSpace_volume_preserving_finTwoCoordinates

set_option autoImplicit false

open MeasureTheory
open EuclideanSpace

theorem solution :
    MeasurePreserving finTwoCoordinatesSwap volume
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  have hswap : MeasurePreserving Prod.swap
      ((volume : Measure ℝ).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    Measure.measurePreserving_swap
  convert hswap.comp volume_preserving_finTwoCoordinates using 1
