-- Prove2me | Theorems.Thm_MovingSofa_positiveVertex_boundedVariation
-- name    : MovingSofa.positiveVertex_boundedVariation
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-10-05T00:11:43.539511+00:00
-- url     : https://prove2.me/theorems/7fc759c0-8de9-4c61-996f-1d13277c6937
-- title:
--   Positive vertex paths have bounded variation
-- statement:
--   The path following the positive vertex of a convex body has bounded variation on every closed interval.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Convex/BoundaryApproximation.lean

import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.Compact
import Definitions.Def_MovingSofa_Geometry_Basic
import Definitions.Def_MovingSofa_Geometry_Contacts
import Definitions.Def_MovingSofa_Geometry_Plane
import Definitions.Def_MovingSofa_Geometry_Contacts
noncomputable section

namespace MovingSofa

theorem positiveVertex_boundedVariation (K : ConvexBody Point) (a b : ℝ) (hab : a ≤ b) :
    BoundedVariationOn (fun t : ℝ ↦ (edgeVertices K (t : Real.Angle)).1) (Set.Icc a b) := by sorry

end MovingSofa
