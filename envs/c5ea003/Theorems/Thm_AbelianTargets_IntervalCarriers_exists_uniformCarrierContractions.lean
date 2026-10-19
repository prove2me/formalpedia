-- Prove2me | Theorems.Thm_AbelianTargets_IntervalCarriers_exists_uniformCarrierContractions
-- name    : AbelianTargets.IntervalCarriers.exists_uniformCarrierContractions
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:48:03.699443+00:00
-- url     : https://prove2.me/theorems/b9c409b9-4fee-4bf0-9b55-1ccf11923b1a
-- title:
--   A common contraction bound works for all bounded carrier widths
-- statement:
--   Let $m,T,S\in\mathbb N$ satisfy $m\ge2$ and $\lfloor\log_m S\rfloor\le T$. Put $D=2(3m+8)(T+1)$. There exists $J\ge0$ such that, for every integer width $R$ with $0<R\le S$, the height-$T$ carrier realization $Z_R$ over $[0,R]$ admits a homotopy $H_R:Z_R\times I\to Z_R$ with basepoint $o_R=\delta_{(0,0)}$ satisfying
--   $$
--   H_R(z,0)=z,\quad H_R(z,1)=o_R,\quad H_R(o_R,t)=o_R,
--   $$
--   $$
--   \operatorname{Lip}(t\mapsto H_R(z,t))\le D,\qquad \operatorname{Lip}(H_R)\le J.
--   $$
--   Joint Lipschitz bounds use the maximum product metric. The same $D,J$ work for all these widths; the contractions themselves may vary with $R$.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific helper: AbelianTargets/UniformCarrierContraction.lean, lines 43–63; SHA256 8f857ef5753408357ac8e08e4f41dfbf4382b936e76df54b4af2ef5fb4005917.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierControlledContraction
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierHeightChain
import Definitions.Def_AT260939824_CarrierHeightDeformation
import Definitions.Def_AT260939824_CommonHeightCarrierContraction
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitBottomCombing
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_JointCarrierRows
import Definitions.Def_AT260939824_LowerCarrierCollapse
import Definitions.Def_AT260939824_OneHeightDeformation
import Definitions.Def_AT260939824_ParallelCollapse
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ProbabilityPushDirac
import Definitions.Def_AT260939824_RealizedBottomCombing
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_TriangleCollapse
import Definitions.Def_AT260939824_UniformCarrierContraction
import Definitions.Def_AT260939824_UpperCarrierCollapse
import Definitions.Def_AT260939824_VariableRowFamilies
import Definitions.Def_AT260939824_VerticalCarrierCollapse
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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousMap.Compact
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

set_option backward.isDefEq.respectTransparency false
namespace AbelianTargets.IntervalCarriers
end AbelianTargets.IntervalCarriers
open AbelianTargets
open AbelianTargets.IntervalCarriers
open scoped NNReal BigOperators

theorem AbelianTargets.IntervalCarriers.exists_uniformCarrierContractions (m : ℕ) (hm : 2 ≤ m) (T S : ℕ)
    (hST : Nat.log m S ≤ T) :
    ∃ J : ℝ≥0,∀ R : ℕ,∀ hR : 0 < R,R ≤ S →
      Nonempty (ControlledContraction
        (point (carrierBase T R) : Realization m T 0 R) (uniformCarrierSpeed m T) J) := by sorry
