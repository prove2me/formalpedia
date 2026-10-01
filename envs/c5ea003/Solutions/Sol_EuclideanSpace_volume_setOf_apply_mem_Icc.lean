-- Prove2me | solution 1 for EuclideanSpace.volume_setOf_apply_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T16:13:42.703768+00:00
-- url     : https://prove2.me/submissions/db34ad47-1104-48be-9e28-c70052468bb9

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_EuclideanSpace_volume_preserving_finTwoCoordinates

set_option autoImplicit false

open MeasureTheory
open EuclideanSpace

theorem solution (l r b t : ℝ) :
    volume {p : EuclideanSpace ℝ (Fin 2) | p 0 ∈ Set.Icc l r ∧ p 1 ∈ Set.Icc b t} =
      ENNReal.ofReal (r - l) * ENNReal.ofReal (t - b) := by
  have h := EuclideanSpace.volume_preserving_finTwoCoordinates.measure_preimage
    ((measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet :
      NullMeasurableSet (Set.Icc l r ×ˢ Set.Icc b t) (volume : Measure (ℝ × ℝ)))
  have step1 : volume {p : EuclideanSpace ℝ (Fin 2) | p 0 ∈ Set.Icc l r ∧ p 1 ∈ Set.Icc b t} =
      volume (Set.Icc l r ×ˢ Set.Icc b t) := by
    convert h using 1
  have step2 : volume (Set.Icc l r ×ˢ Set.Icc b t) =
      ENNReal.ofReal (r - l) * ENNReal.ofReal (t - b) := by
    simp only [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
  exact step1.trans step2
