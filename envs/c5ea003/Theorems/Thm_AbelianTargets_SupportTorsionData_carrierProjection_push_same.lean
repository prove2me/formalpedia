-- Prove2me | Theorems.Thm_AbelianTargets_SupportTorsionData_carrierProjection_push_same
-- name    : AbelianTargets.SupportTorsionData.carrierProjection_push_same
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:38:57.822987+00:00
-- url     : https://prove2.me/theorems/8aa45417-bc44-42fb-97a8-f3132c3adf4a
-- title:
--   Carrier projection is independent of carrier enlargement
-- statement:
--   Let $H$ be a finite graph and $D$ its support-torsion data, with presentation base $m=2D.\mathrm{power}+1$. Consider two finite interval carriers and a map $f$ between their vertex types that preserves the underlying coordinate pair $(r,j)$. Assume the first carrier cell set is contained in the second and that a realization map $i$ has probability coordinates $i(p)=f_*p$. Then
--   $$D.\pi(i(p))=D.\pi(p).$$
--   Here $D.\pi$ denotes the projection for the relevant carrier parameters.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Sections 3–6 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. This helper is formalization-specific infrastructure, not a separately numbered assertion of the paper. Original Lean proof: AbelianTargets/CarrierProjectionNaturality.lean, lines 94–113; raw UTF-8 source SHA-256 098cf99628dbcf5d3315c1c13b46758f2d7d51cafb5296e03ece61be272fd7d8. No public source repository commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierIntervalInclusion
import Definitions.Def_AT260939824_CarrierProjectionGluing
import Definitions.Def_AT260939824_CarrierProjectionNaturality
import Definitions.Def_AT260939824_CarrierSupportProjection
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_DoubleCoverLifts
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
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

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
attribute [local instance] Classical.propDecidable
namespace AbelianTargets.SupportTorsionData
end AbelianTargets.SupportTorsionData
open AbelianTargets
open AbelianTargets.SupportTorsionData
open IntervalCarriers
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)

theorem AbelianTargets.SupportTorsionData.carrierProjection_push_same {K T : ℕ} {A B C E : ℤ}
    (f : CarrierVertex K A B → CarrierVertex T C E) (hf : ∀v,(f v).1=v.1)
    (hc : carrierCells (2*D.power+1) K A B ⊆ carrierCells (2*D.power+1) T C E)
    (i : Realization (2*D.power+1) K A B → Realization (2*D.power+1) T C E)
    (hi : ∀p,(i p).1=Probability.push f p.1)
    (p : Realization (2*D.power+1) K A B) : D.carrierProjection T C E (i p)=D.carrierProjection K A B p := by sorry
