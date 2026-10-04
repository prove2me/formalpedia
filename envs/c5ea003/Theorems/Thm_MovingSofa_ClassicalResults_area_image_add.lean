-- Prove2me | Theorems.Thm_MovingSofa_ClassicalResults_area_image_add
-- name    : MovingSofa.ClassicalResults.area_image_add
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-10-03T14:45:54.907064+00:00
-- url     : https://prove2.me/theorems/b822c213-c08e-40b2-b7c6-7312a2ac6ed4
-- title:
--   Planar area is translation invariant
-- statement:
--   Translating a planar set does not change its Lebesgue area. Follows from the image/preimage translation lemmas for Haar volume.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Classical/Area.lean#L22-L30

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Definitions.Def_MovingSofa_Classical_Area
open MeasureTheory Set
open MovingSofa.ClassicalResults

namespace MovingSofa.ClassicalResults

theorem area_image_add (S : Set Plane) (v : Plane) :
    area ((fun p ↦ p + v) '' S) = area S := by sorry

end MovingSofa.ClassicalResults
