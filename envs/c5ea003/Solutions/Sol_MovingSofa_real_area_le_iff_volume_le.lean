-- Prove2me | solution 1 for MovingSofa.real_area_le_iff_volume_le
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-10-03T15:56:52.890769+00:00
-- url     : https://prove2.me/submissions/ed2a849f-241d-4e7d-b5ef-42a24fd39378

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Definitions.Def_MovingSofa_Classical_Area

set_option autoImplicit false

open MeasureTheory
open MovingSofa.ClassicalResults

theorem solution (s t : Set Plane)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfinS : volume s < ⊤) (hfinT : volume t < ⊤) :
    MovingSofa.ClassicalResults.area s ≤ MovingSofa.ClassicalResults.area t ↔ volume s ≤ volume t := by
  clear hs ht
  exact ENNReal.toReal_le_toReal hfinS.ne hfinT.ne
