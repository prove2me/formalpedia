-- Prove2me | Theorems.Thm_AbelianTargets_SupportTorsionData_faceValue_affine_representation
-- name    : AbelianTargets.SupportTorsionData.faceValue_affine_representation
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:48:42.230866+00:00
-- url     : https://prove2.me/theorems/e773395c-94b5-4b13-a0bb-e16ef20f890a
-- title:
--   Every carrier face chart has one affine representation
-- statement:
--   For support-torsion data $D$ of a finite graph $H$, fix any finite interval carrier and an admissible simplex face $s$ of its realization. There are an integer $r$ and vertex functions $h,\theta$ into $[0,1]$ such that every distribution $p$ supported on $s$ satisfies
--   $$\mathrm{faceValue}_s(p)=\sigma^r A_D(h,\theta;p).$$
--   The chosen functions and parity shift depend on the face, and the identity holds for all probability points of that face.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Sections 3–6 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. This helper is formalization-specific infrastructure, not a separately numbered assertion of the paper. Original Lean proof: AbelianTargets/CarrierProjectionFaceCharts.lean, lines 13–63; raw UTF-8 source SHA-256 ced801faf30eedc51be86cbe61ecc2a93db401f07035a71e5707984d6d7e12ba. No public source repository commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierProjectionGluing
import Definitions.Def_AT260939824_CarrierSupportProjection
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_DoubleCoverLifts
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_ParitySwapGeometry
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ProbabilityParameters
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SegmentedOddPath
import Definitions.Def_AT260939824_SimplicialChartGluing
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_SupportPathClasses
import Definitions.Def_AT260939824_SupportRelationCharts
import Definitions.Def_AT260939824_SupportWitness
import Definitions.Def_AT260939824_TopologicalWalks
import Definitions.Def_AT260939824_VariableRowFamilies
import Definitions.Def_AT260939824_WordPathHelpers
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
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
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FieldSimp
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
import Mathlib.Topology.LocallyFinite
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

namespace AbelianTargets.SupportTorsionData
end AbelianTargets.SupportTorsionData
open AbelianTargets
open AbelianTargets.SupportTorsionData
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)
open IntervalCarriers

theorem AbelianTargets.SupportTorsionData.faceValue_affine_representation (K : ℕ) (A B : ℤ) (s : Finset (CarrierVertex K A B))
    (hs : s∈simplexFaces (2*D.power+1) K A B) :
    ∃ (r:ℤ) (height theta:CarrierVertex K A B→I),
      ∀p:Probability (CarrierVertex K A B),p.SupportedOn (s:Set _)→
        (D.projectionCharts K A B).faceValue s p=
          SupportPair.paritySwap H r (D.affineChart height theta p) := by sorry
