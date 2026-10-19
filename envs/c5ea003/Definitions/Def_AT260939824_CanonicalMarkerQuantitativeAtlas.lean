-- Prove2me | Definitions.Def_AT260939824_CanonicalMarkerQuantitativeAtlas
-- name    : AT260939824_CanonicalMarkerQuantitativeAtlas
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:31:23.919991+00:00
-- url     : https://prove2.me/theorems/995a1f63-7cae-48f3-aeae-56e479a8e71f
-- title:
--   Canonical quantitative atlas recursion from one contraction family
-- statement:
--   Let continuous marker-box data determine the retained tiling at $x$, with coordinate scales $L_j\ge1$ and $S\ge24$. Fix $m,K,i$ and one normalized contraction family on all positive widths at most $6L_i$, with joint bound $J$. The canonical quantitative skeleton is the rank recursion driven by the transported members of this family.
--
--   Its rates use lower widths $L_j/[32(2S+1)^d]$, upper widths $6L_j$, and the uniform carrier speed for $m,K$. The definition returns endpoint-preserving compatible carrier maps at every requested rank threshold. It supplies a fixed choice of maps across cells and action points once the normalized family has been selected.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4–6; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization; its implementation definitions are not asserted to be separately numbered in the paper. Original Lean module AbelianTargets/CanonicalMarkerQuantitativeAtlas.lean, selected declaration lines 11-21; SHA-256 e4c772625643345a36c17bf6bc449123c9afed06e1a12f4da53a4c15bb21aa39. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_ActualMarkerAtlas
import Definitions.Def_AT260939824_ActualMarkerQuantitativeAtlas
import Definitions.Def_AT260939824_ActualQuantitativeAtlasRecursion
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasCanonicalContractions
import Definitions.Def_AT260939824_AtlasEndpointRecursion
import Definitions.Def_AT260939824_AtlasQuantitativeRecursion
import Definitions.Def_AT260939824_AtlasRankRecursion
import Definitions.Def_AT260939824_AtlasRelativeCellExtension
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CanonicalIntervalContractions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierControlledContraction
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierHeightChain
import Definitions.Def_AT260939824_CarrierHeightDeformation
import Definitions.Def_AT260939824_CarrierIntervalInclusion
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_CommonHeightCarrierContraction
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ConeDomainNaturality
import Definitions.Def_AT260939824_ContinuousAtlasPatterns
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_ControlledCone
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_DigitBottomCombing
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntegerGridIntervals
import Definitions.Def_AT260939824_IntegerPrismChart
import Definitions.Def_AT260939824_IntegerPrismFilling
import Definitions.Def_AT260939824_IntegerPrismTranslation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_JointCarrierRows
import Definitions.Def_AT260939824_LowerCarrierCollapse
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerPriorities
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AT260939824_OneHeightDeformation
import Definitions.Def_AT260939824_OrbitMarkerCuts
import Definitions.Def_AT260939824_ParallelCollapse
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_PriorityCuts
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ProbabilityPushDirac
import Definitions.Def_AT260939824_RealizedBottomCombing
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_RectangularAtlasBoundary
import Definitions.Def_AT260939824_RectangularBoundaryStrata
import Definitions.Def_AT260939824_RectangularCells
import Definitions.Def_AT260939824_RectangularCone
import Definitions.Def_AT260939824_RectangularTranslation
import Definitions.Def_AT260939824_RegularAnisotropicAtlas
import Definitions.Def_AT260939824_RelativeContractionNaturality
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
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
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
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
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

namespace AbelianTargets
noncomputable section
open scoped NNReal
variable {d : ℕ} {L : Fin d→ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M₀ : AnisotropicClopenMarkers d L X} {S : ℕ}

/-- Literal atlas rank recursion driven by one fixed zero-based contraction
family. The provider makes no further choice on individual cells. -/
def ContinuousMarkerBoxes.canonicalQuantitativeSkeleton
    (B : ContinuousMarkerBoxes M₀ S) (hL : ∀j,1≤L j) (hS : 24≤S) (x : X)
    (m K : ℕ) (i : Fin d) (J : ℝ≥0)
    (H : IntervalCarriers.NormalizedContractionFamily m K (6*L i) J) (n : ℕ) :
    QuantitativeEndpointSkeletonCarrierMaps (B.tiling hL (by omega) x) m K i n
      (atlasRankRates (fun j=>(L j : ℝ≥0)/(32*((2*S+1)^d : ℕ)))
        (fun j=>6*(L j : ℝ≥0)) (IntervalCarriers.uniformCarrierSpeed m K) J i n) :=
  B.quantitativeSkeleton hL hS x m K i (IntervalCarriers.uniformCarrierSpeed m K) J
    (canonicalAtlasContractionProvider H (B.tiling hL (by omega) x) i (by rfl)) n

end
end AbelianTargets


