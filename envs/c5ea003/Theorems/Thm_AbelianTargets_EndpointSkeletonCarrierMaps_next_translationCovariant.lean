-- Prove2me | Theorems.Thm_AbelianTargets_EndpointSkeletonCarrierMaps_next_translationCovariant
-- name    : AbelianTargets.EndpointSkeletonCarrierMaps.next_translationCovariant
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:38:05.382123+00:00
-- url     : https://prove2.me/theorems/acd23111-e21d-40ab-a03e-521ad61066a6
-- title:
--   Translation covariance passes to the next skeleton rank
-- statement:
--   Let $T,U$ be bounded integer rectangular tilings in dimension $d$, possibly with different side bounds. Fix natural carrier parameters $m,K$, a coordinate $i$, and $n\in\mathbb N$. Let $F,G$ be compatible continuous interval-carrier maps on cells of $T,U$ of rank less than $n$, preserving the prescribed left and right endpoints. Let $a\in\mathbb Z^d$, and suppose every cell $R$ of $T$ has $R+a$ as a cell of $U$. Assume the old maps satisfy $G_{R+a}(z+a)=T_{a_i}F_R(z)$. For each tiling choose compatible endpoint-preserving extensions on all rank-$n$ cells, agreeing with the old boundary maps, and suppose these new extensions satisfy the same equality. Then
--   $$G^{+}_{R+a}(z+a)=T_{a_i}F^{+}_R(z)\qquad
--   (R\in\operatorname{Cells}(T),\ \operatorname{rank}R<n+1,\ z\in R),$$
--   where $F^+,G^+$ are the next-rank skeleton maps and $T_{a_i}$ is horizontal carrier translation.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific helper: AbelianTargets/AtlasRankCovariance.lean, lines 36–59; SHA256 1b7d3f270e8a2cbef3162652c54692490ae3409c6dcf937ce7956d237c34bb80.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasEndpointRecursion
import Definitions.Def_AT260939824_AtlasRankCovariance
import Definitions.Def_AT260939824_AtlasRankRecursion
import Definitions.Def_AT260939824_AtlasRelativeCellExtension
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierIntervalInclusion
import Definitions.Def_AT260939824_CarrierProjectionGluing
import Definitions.Def_AT260939824_CarrierProjectionNaturality
import Definitions.Def_AT260939824_CarrierTranslationGeometry
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ContinuousAtlasPatterns
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_ControlledCone
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_DoubleCoverLifts
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntegerGridIntervals
import Definitions.Def_AT260939824_IntegerPrismChart
import Definitions.Def_AT260939824_IntegerPrismFilling
import Definitions.Def_AT260939824_IntegerPrismTranslation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerPriorities
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AT260939824_OrbitMarkerCuts
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_PriorityCuts
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ProbabilityParameters
import Definitions.Def_AT260939824_ProbabilityPushDirac
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_RectangularAtlasBoundary
import Definitions.Def_AT260939824_RectangularBoundaryStrata
import Definitions.Def_AT260939824_RectangularCells
import Definitions.Def_AT260939824_RectangularCone
import Definitions.Def_AT260939824_RectangularTranslation
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_RegularAnisotropicAtlas
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
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.LocallyConstant.Basic
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

/-! Translation covariance propagates through the literal rank recursion. -/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace AbelianTargets.EndpointSkeletonCarrierMaps
end AbelianTargets.EndpointSkeletonCarrierMaps
open AbelianTargets
open AbelianTargets.EndpointSkeletonCarrierMaps
variable {d:ℕ} {K₀ K₁:Fin d→ℕ}
variable {T:IntegerRectangularTiling d K₀} {U:IntegerRectangularTiling d K₁}
variable {m K n:ℕ} {i:Fin d}
variable (F:EndpointSkeletonCarrierMaps T m K i n) (G:EndpointSkeletonCarrierMaps U m K i n)

theorem AbelianTargets.EndpointSkeletonCarrierMaps.next_translationCovariant (a:Fin d→ℤ)
    (hcell:∀R:RectangularCell d,R∈T.cells→R.translate a∈U.cells)
    (hold:SkeletonCarrierMaps.TranslationCovariant F.toSkeletonCarrierMaps G.toSkeletonCarrierMaps a hcell)
    (extendF:∀(R:RectangularCell d)(hR:R∈T.cells)(he:R.rank=n),
      EndpointCellCarrierExtension (F.toSkeletonCarrierMaps.lowerFamily R he) hR)
    (extendG:∀(R:RectangularCell d)(hR:R∈U.cells)(he:R.rank=n),
      EndpointCellCarrierExtension (G.toSkeletonCarrierMaps.lowerFamily R he) hR)
    (hnew:∀(R:RectangularCell d)(hR:R∈T.cells)(he:R.rank=n)(z:CellClosedDomain R),
      (extendG (R.translate a) (hcell R hR) (by simpa only [RectangularCell.rank_translate] using he)).map (R.translateClosedPoint a z)=
        IntervalCarriers.realizationTranslation (a i) ((extendF R hR he).map z)) :
    SkeletonCarrierMaps.TranslationCovariant (F.next extendF).toSkeletonCarrierMaps
      (G.next extendG).toSkeletonCarrierMaps a hcell := by sorry
