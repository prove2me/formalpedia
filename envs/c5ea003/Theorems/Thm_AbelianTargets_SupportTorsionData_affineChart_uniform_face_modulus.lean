-- Prove2me | Theorems.Thm_AbelianTargets_SupportTorsionData_affineChart_uniform_face_modulus
-- name    : AbelianTargets.SupportTorsionData.affineChart_uniform_face_modulus
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:49:10.195619+00:00
-- url     : https://prove2.me/theorems/aefcd70b-1196-434b-996f-ca302c7f04ea
-- title:
--   A uniform modulus for all three-vertex affine charts
-- statement:
--   Let $D$ be support-torsion data for a finite graph $H$. For every $\varepsilon>0$, there is $\delta>0$ with the following uniform property. For any finite set $V$, functions $h,\theta:V\to[0,1]$, integer $r$, and distributions $p,q$ supported on one set of at most three vertices,
--   $$d(p,q)<\delta\ \Longrightarrow\ d(\sigma^r A_D(h,\theta;p),\sigma^r A_D(h,\theta;q))<\varepsilon.$$
--   Here $A_D$ is the affine support chart and $\sigma$ is the shore swap. The same $\delta$ works for all these choices.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Sections 3–6 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. This helper is formalization-specific infrastructure, not a separately numbered assertion of the paper. Original Lean proof: AbelianTargets/UniformAffineSupportCharts.lean, lines 40–62; raw UTF-8 source SHA-256 97ba5022a771ec9935b2ee2f163000db7fb6b64a8f3cd4d14e74cbce48b288a7. No public source repository commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
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

/-! A common modulus for all torsion charts, independent of the vertex set. -/
universe v
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
open scoped unitInterval
attribute [local instance] Classical.propDecidable
namespace AbelianTargets.SupportTorsionData
end AbelianTargets.SupportTorsionData
open AbelianTargets
open AbelianTargets.SupportTorsionData
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)

theorem AbelianTargets.SupportTorsionData.affineChart_uniform_face_modulus :
    ∀ ε:ℝ,0<ε→∃δ:ℝ,0<δ ∧
      ∀ {V:Type v} [Fintype V] (height theta:V→I) (r:ℤ) (s:Finset V)
        (p q:Probability V),s.card≤3→p.SupportedOn (s:Set V)→q.SupportedOn (s:Set V)→
        dist p q<δ→dist (SupportPair.paritySwap H r (D.affineChart height theta p))
          (SupportPair.paritySwap H r (D.affineChart height theta q))<ε := by sorry
