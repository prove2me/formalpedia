-- Prove2me | Theorems.Thm_MovingSofa_real_area_le_iff_volume_le
-- name    : MovingSofa.real_area_le_iff_volume_le
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-10-03T15:56:46.580164+00:00
-- url     : https://prove2.me/theorems/55cea5f3-7c10-4a42-b006-126260c36f29
-- title:
--   Classical area comparison iff volume comparison
-- statement:
--   For measurable finite-volume planar sets, $area(s)\le area(t)$ iff $volume(s)\le volume(t)$: both sides are the same inequality transported by $toReal$. Source: Motion/CanonicalBridge.lean, used in the upper-bound transport.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Motion/CanonicalBridge.lean#L92-L97

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Definitions.Def_MovingSofa_Classical_Area
open MeasureTheory
open MovingSofa.ClassicalResults

namespace MovingSofa

theorem real_area_le_iff_volume_le (s t : Set Plane)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfinS : volume s < ⊤) (hfinT : volume t < ⊤) :
    ClassicalResults.area s ≤ ClassicalResults.area t ↔ volume s ≤ volume t := by sorry

end MovingSofa
