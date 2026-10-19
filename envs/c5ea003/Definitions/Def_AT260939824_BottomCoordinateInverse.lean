-- Prove2me | Definitions.Def_AT260939824_BottomCoordinateInverse
-- name    : AT260939824_BottomCoordinateInverse
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:08:33.407003+00:00
-- url     : https://prove2.me/theorems/91dea7fe-9a90-4412-af36-ae7d52a92d3c
-- title:
--   Barycentric coordinates on the bottom carrier interval
-- statement:
--   Let $p$ be a probability distribution on vertices $(r,h)$ of the carrier over $[0,R]$ with height bound $K$. Its bottom coordinate is
--
--   $$ b(p)=\sum_v p(v)r(v). $$
--
--   The bottom-support predicate restricts the support to one height-zero vertex or two consecutive height-zero vertices. These definitions identify the geometric bottom edge interval inside the probability realization and provide its scalar coordinate.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/BottomCoordinateInverse.lean, selected declaration lines 11-12, 87-90; SHA-256 180b5db23587fbd2d4966db9ba2b4276f31d76a8404df22100f135715f0e0dc9. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CompressedCarrierWalks
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_JointCarrierRows
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityTwoVertices
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_VariableRowFamilies
import Definitions.Def_AT260939824_WordPathHelpers
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

/-! The actual affine bottom interval is inverted by its barycentric
horizontal coordinate, on every singleton and unit bottom edge. -/

namespace AbelianTargets.IntervalCarriers
noncomputable section
open scoped BigOperators NNReal unitInterval

def bottomCoordinate (K R : ℕ) (p : Probability (CarrierVertex K 0 R)) : ℝ :=
  p.weightedCoordinate (fun v => (v.val.1 : ℝ))















def BottomSupported (K R : ℕ) (p : Probability (CarrierVertex K 0 R)) : Prop :=
  (∃ n : ℕ,∃ hn : n ≤ R,p.SupportedOn ({bottomVertex K R n hn} : Set _)) ∨
    ∃ n : ℕ,∃ hn : n < R,p.SupportedOn ({bottomVertex K R n hn.le,
      bottomVertex K R (n+1) (by omega)} : Set _)



end
end AbelianTargets.IntervalCarriers


