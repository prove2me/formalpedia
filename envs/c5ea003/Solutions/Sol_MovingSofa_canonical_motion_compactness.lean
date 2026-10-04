-- Prove2me | solution 1 for MovingSofa.canonical_motion_compactness
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-10-03T19:30:36.573354+00:00
-- url     : https://prove2.me/submissions/1de28cb0-d144-455b-966d-4b52d39d9c7c

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.TotallyDisconnected
import Definitions.Def_MovingSofa_Basic
import Definitions.Def_MovingSofa_Geometry_Rotation
import Theorems.Thm_MovingSofa_IsMovingSofa_isBounded

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped unitInterval
open MovingSofa

theorem solution (s : Set MovingSofa.Point) (m : I → MovingSofa.Point ≃ᵃⁱ[ℝ] MovingSofa.Point)
    (h : MovingSofa.IsMovingSofa s m) :
    IsCompact s ∧ MeasurableSet s ∧ volume s < ⊤ := by
  have hc : IsCompact s := Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨h.isClosed, MovingSofa.IsMovingSofa.isBounded h⟩
  exact ⟨hc, hc.measurableSet, hc.measure_lt_top⟩
