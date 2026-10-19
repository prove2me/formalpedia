-- Prove2me | Theorems.Thm_AbelianTargets_IntervalCarriers_NormalizedContractionFamily_atWidthInterval_shift
-- name    : AbelianTargets.IntervalCarriers.NormalizedContractionFamily.atWidthInterval_shift
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:38:26.743032+00:00
-- url     : https://prove2.me/theorems/7cdf7d76-38cc-47d2-ad9e-61f4a9cda328
-- title:
--   Normalized interval contractions commute with integer translation
-- statement:
--   Fix natural numbers $m,K,S$, $J\ge0$, and a normalized contraction family: for each $0<n\le S$, a basepoint-fixing contraction of the height-$K$ carrier over $[0,n]$ with track bound $2(3m+8)(K+1)$ and common joint bound $J$. Let $A,B,C,D,a\in\mathbb Z$ and $n\in\mathbb N$ satisfy $0<n\le S$, $n+A=B$, $A+a=C$, and $B+a=D$. Write $T_a$ for the isometric carrier translation that sends vertex $(x,h)$ to $(x+a,h)$, and $H_{[A,B]}$ for the normalized contraction transported from width $n$. Then
--   $$
--   H_{[C,D]}(T_a p,t)=T_a(H_{[A,B]}(p,t))
--   \quad(p\in Z_{[A,B]},\ t\in I).
--   $$
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific helper: AbelianTargets/CanonicalIntervalContractions.lean, lines 112–131; SHA256 cc01dd1d372355303d406b778860f637168990e0fc875320e076a01b859e4796.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CanonicalIntervalContractions
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

/-! Contractions are selected once at zero-based interval widths and then
transported by an explicit isometry. The normalized data are retained as
data rather than being reselected from an existential proof at every cell. -/
namespace AbelianTargets.IntervalCarriers
end AbelianTargets.IntervalCarriers
open AbelianTargets
open AbelianTargets.IntervalCarriers
open scoped unitInterval NNReal
variable {m K S : ℕ} {J : ℝ≥0}

theorem AbelianTargets.IntervalCarriers.NormalizedContractionFamily.atWidthInterval_shift
    (H : NormalizedContractionFamily m K S J) (n : ℕ) (hn : 0<n) (hS : n≤S)
    (A B C D a : ℤ) (hb : (n:ℤ)+A=B) (hA : A+a=C) (hB : B+a=D)
    (p : Realization m K A B) (t : I) :
    (H.atWidthInterval n hn hS C D (by omega)).map (intervalShiftEquiv a hA hB p,t)=
      intervalShiftEquiv a hA hB ((H.atWidthInterval n hn hS A B hb).map (p,t)) := by sorry
