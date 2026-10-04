-- Prove2me | Definitions.Def_MovingSofa_Classical_Area
-- name    : MovingSofa_Classical_Area
-- status  : Definition
-- author  : @Tamas Fulop
-- created : 2026-10-03T14:35:29.130238+00:00
-- url     : https://prove2.me/theorems/b68f6c3b-cfca-4f74-b096-0ac6f60723aa
-- title:
--   Classical planar area
-- statement:
--   The Euclidean plane and the real-valued Lebesgue area of a planar set (volume coerced to reals). The bridge notion between classical area comparisons and measure volumes on the road to the area-volume comparison.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Classical/Area.lean#L15-L19

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Algebra.Group.Pointwise.Set.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace MovingSofa.ClassicalResults

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The real-valued Lebesgue area of a planar set. -/
def area (s : Set Plane) : ℝ := (volume s).toReal

end MovingSofa.ClassicalResults


