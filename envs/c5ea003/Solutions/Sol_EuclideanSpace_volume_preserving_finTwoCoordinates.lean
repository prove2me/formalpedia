-- Prove2me | solution 1 for EuclideanSpace.volume_preserving_finTwoCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T16:04:35.028712+00:00
-- url     : https://prove2.me/submissions/fe69a7a8-f630-4a44-aad3-f11c92fbaca5

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false

open MeasureTheory

theorem solution :
    MeasurePreserving (fun p : EuclideanSpace ℝ (Fin 2) ↦ (p 0, p 1)) volume volume := by
  exact (volume_preserving_finTwoArrow ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))
