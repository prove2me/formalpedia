-- Prove2me | Theorems.Thm_AbelianTargets_IntervalCarriers_bottomFinish_joint
-- name    : AbelianTargets.IntervalCarriers.bottomFinish_joint
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:44:11.078135+00:00
-- url     : https://prove2.me/theorems/77c690b4-0183-4642-9604-8bd3a86dc515
-- title:
--   The bottom finishing homotopy is jointly Lipschitz
-- statement:
--   Let $m\ge2$ and $R>0$ be natural numbers, $K=\lfloor\log_m R\rfloor$, and $Z$ the realization of the interval carrier of height $K$ over $[0,R]$, equipped with its mass-coordinate metric. Let $H$ be the height-deformation homotopy, let $x(z)$ be the horizontal barycentric coordinate of $H(z,1)$, and let $\widehat B$ be the realized bottom combing. Define $F(z,t)=\widehat B(x(z),1-t)$. Then
--   $$
--   \exists J\ge0\quad \operatorname{dist}(F(z,t),F(z',t'))\le J\max\{\operatorname{dist}(z,z'),|t-t'|\}
--   \quad(z,z'\in Z,\ t,t'\in I).
--   $$
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific helper: AbelianTargets/CarrierControlledContraction.lean, lines 44–56; SHA256 b384a237cd56abeebbb0755c82c8fa158650459e789f7a29253115142955b90c.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierControlledContraction
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierHeightChain
import Definitions.Def_AT260939824_CarrierHeightDeformation
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
import Definitions.Def_AT260939824_RealizedBottomCombing
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_TriangleCollapse
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
set_option maxHeartbeats 800000
/-! An actual controlled contraction of the finite triangulated interval
carrier. Every track has logarithmic speed; the joint constant is finite. -/
namespace AbelianTargets.IntervalCarriers
end AbelianTargets.IntervalCarriers
open AbelianTargets
open AbelianTargets.IntervalCarriers
open scoped NNReal

theorem AbelianTargets.IntervalCarriers.bottomFinish_joint (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R) :
    ∃ J : ℝ≥0, LipschitzWith J (bottomFinish m hm R hR) := by sorry
