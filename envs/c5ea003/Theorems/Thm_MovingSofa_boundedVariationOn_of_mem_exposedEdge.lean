-- Prove2me | Theorems.Thm_MovingSofa_boundedVariationOn_of_mem_exposedEdge
-- name    : MovingSofa.boundedVariationOn_of_mem_exposedEdge
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-10-05T00:11:29.123996+00:00
-- url     : https://prove2.me/theorems/a58aacea-51f0-4cb9-bba5-a562af388bb2
-- title:
--   Exposed-edge selections have bounded variation
-- statement:
--   Every selection of points from the exposed edges of a convex body has bounded variation on bounded intervals.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Convex/BoundaryVariation.lean

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

theorem boundedVariationOn_of_mem_exposedEdge (K : ConvexBody Point)
    (f : ℝ → Point) (hf : ∀ t : ℝ, f t ∈ exposedEdge K (t : Real.Angle)) (a b : ℝ) :
    BoundedVariationOn f (Set.Icc a b) := by sorry

end MovingSofa
