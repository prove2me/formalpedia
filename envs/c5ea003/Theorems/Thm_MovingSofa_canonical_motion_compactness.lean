-- Prove2me | Theorems.Thm_MovingSofa_canonical_motion_compactness
-- name    : MovingSofa.canonical_motion_compactness
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-10-03T19:04:10.203456+00:00
-- url     : https://prove2.me/theorems/f3f64fca-9715-47c9-86c6-b19665515928
-- title:
--   Moving sofas are compact, measurable, finite-volume
-- statement:
--   Every set admitting a hallway motion is compact (closed plus bounded), hence measurable with finite volume. Reduction over boundedness; source: Motion/CanonicalBridge.lean.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Motion/CanonicalBridge.lean#L85-L90

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.TotallyDisconnected
import Definitions.Def_MovingSofa_Basic
import Definitions.Def_MovingSofa_Geometry_Rotation
open Set MeasureTheory
open scoped unitInterval

namespace MovingSofa

theorem canonical_motion_compactness (s : Set Point) (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (h : IsMovingSofa s m) :
    IsCompact s ∧ MeasurableSet s ∧ volume s < ⊤ := by sorry

end MovingSofa
