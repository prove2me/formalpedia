-- Prove2me | solution 1 for MovingSofa.ClassicalResults.area_image_add
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-10-03T14:46:05.364528+00:00
-- url     : https://prove2.me/submissions/9800fc2b-4845-474b-b701-9db2a1b0de86

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Definitions.Def_MovingSofa_Classical_Area

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open MovingSofa.ClassicalResults

theorem solution (S : Set Plane) (v : Plane) :
    area ((fun p ↦ p + v) '' S) = area S := by
  change (MeasureTheory.volume ((fun p ↦ p + v) '' S)).toReal =
    (MeasureTheory.volume S).toReal
  rw [Set.image_add_right]
  have hf : (fun x : Plane ↦ x + -v) = fun x ↦ -v + x := by
    funext x
    exact add_comm x (-v)
  rw [hf, MeasureTheory.measure_preimage_add]
