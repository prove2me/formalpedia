-- Prove2me | Definitions.Def_AT260939824_CarrierProjectionNaturality
-- name    : AT260939824_CarrierProjectionNaturality
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:31:57.158442+00:00
-- url     : https://prove2.me/theorems/b34ecaa2-8e88-4875-8cce-aa5f61377402
-- title:
--   The projection of a carrier vertex is determined by its horizontal parity
-- statement:
--   Let $H$ be a finite graph with support torsion data $D$, whose basepoint in the compatible-probability-pair space is $p$ and whose positive exponent is $k$. Put $m=2k+1$. For any natural height $K$, integer interval bounds $A,B$, and carrier vertex $v=(r,h)$ with $A\le r\le B$ and $h\le K$, the carrier projection satisfies
--   $$\pi_{D,K,A,B}(\delta_v)=\tau^{\,r\bmod2}(p),$$
--   where $\tau$ interchanges the two probability shores. Thus a vertex's image depends only on the parity of its horizontal coordinate, including negative coordinates; it is independent of its height. This is the vertex compatibility law for carrier inclusions and translations.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/CarrierProjectionNaturality.lean, selected declaration lines 81-92; SHA-256 098cf99628dbcf5d3315c1c13b46758f2d7d51cafb5296e03ece61be272fd7d8. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierIntervalInclusion
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
import Definitions.Def_AT260939824_SupportSkeletonMap
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
noncomputable section
attribute [local instance] Classical.propDecidable

namespace IntervalCarriers













end IntervalCarriers

namespace SupportTorsionData
open IntervalCarriers
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)

@[simp] theorem carrierProjection_point {K : ℕ} {A B : ℤ} (v : CarrierVertex K A B) :
    D.carrierProjection K A B (point v)=SupportPair.paritySwap H v.1.1 D.base := by
  have hp : (Probability.dirac v).SupportedOn ({v} : Set (CarrierVertex K A B)) :=
    Probability.supportedOn_dirac v (by simp)
  have hraw : RawSupported (point v : Realization (2*D.power+1) K A B).1 {v.1} := by
    intro w hw
    have he : w=v := hp w hw
    simp [he]
  have hsk : SkeletonSupported (m := 2*D.power+1) (point v : Realization (2*D.power+1) K A B).1 :=
    Or.inl ⟨v.1,v.2,hraw⟩
  rw [carrierProjection,(D.projectionCharts K A B).eval_eq_skeleton (by omega) _ hsk]
  exact D.skeletonMap_singleton Subtype.val _ v hp









end SupportTorsionData
end
end AbelianTargets


