-- Prove2me | Definitions.Def_AT260939824_DeterministicQuantitativeAtlas
-- name    : AT260939824_DeterministicQuantitativeAtlas
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:16:35.908012+00:00
-- url     : https://prove2.me/theorems/99c5e2b4-6e21-435d-bd44-6da08050af58
-- title:
--   Deterministic quantitative skeleton extension
-- statement:
--   For a rectangular atlas in dimension $d$, a distinguished coordinate $i$, and endpoint carrier maps on its lower skeleton, this bundle defines the actual next-rank extension using controlled contractions on the cells. Positive lower side bounds $\delta_j$, upper bounds $U_j$, and contraction constants determine the recursively updated coordinate rates. Iterating the construction produces maps on every skeleton with those prescribed rates.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/DeterministicQuantitativeAtlas.lean, selected declaration lines 12-23, 25-52, 54-62, 64-72; SHA-256 9ce4fcadfe40ffca8a0c5583862984e87ee7f7e836392af11425dbf0fc88f408. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_ActualQuantitativeAtlasRecursion
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoundaryPathBounds
import Definitions.Def_AT260939824_AtlasBoundaryTransverseBounds
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasCarrierEndpoints
import Definitions.Def_AT260939824_AtlasControlledCellExtension
import Definitions.Def_AT260939824_AtlasEndpointRecursion
import Definitions.Def_AT260939824_AtlasQuantitativeRecursion
import Definitions.Def_AT260939824_AtlasRankRecursion
import Definitions.Def_AT260939824_AtlasRelativeCellExtension
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierIntervalInclusion
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ContinuousAtlasPatterns
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_ControlledCone
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntegerGridIntervals
import Definitions.Def_AT260939824_IntegerPrismChart
import Definitions.Def_AT260939824_IntegerPrismEstimates
import Definitions.Def_AT260939824_IntegerPrismFilling
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
import Definitions.Def_AT260939824_ProbabilityPushDirac
import Definitions.Def_AT260939824_RectangularAtlasBoundary
import Definitions.Def_AT260939824_RectangularBoundaryStrata
import Definitions.Def_AT260939824_RectangularCells
import Definitions.Def_AT260939824_RectangularCone
import Definitions.Def_AT260939824_RectangularTranslation
import Definitions.Def_AT260939824_RegularAnisotropicAtlas
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
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

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace AbelianTargets
noncomputable section
open scoped NNReal
variable {d : ℕ} {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d}

def actualQuantitativeExtension {n : ℕ} {C : Fin d→ℝ≥0}
    (F : QuantitativeEndpointSkeletonCarrierMaps T m K i n C) {D J : ℝ≥0}
    (H : ∀R,R∈T.cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint m K i R) D J)
    (R : RectangularCell d) (hR : R∈T.cells) (he : R.rank=n) :
    EndpointCellCarrierExtension (F.toSkeletonCarrierMaps.lowerFamily R he) hR :=
  if hi : R.lower i<R.upper i then
    (F.toSkeletonCarrierMaps.lowerFamily R he).controlledCellExtension hR
      (F.toEndpointSkeletonCarrierMaps.lowerFamily_endpoints R he) C
      (F.lowerFamily_update_bounds R he) hi (H R hR hi)
  else (F.toSkeletonCarrierMaps.lowerFamily R he).collapsedCellExtension hR
    (F.toEndpointSkeletonCarrierMaps.lowerFamily_endpoints R he)
    (le_antisymm (R.ordered i) (le_of_not_gt hi))

theorem actualQuantitativeExtension_bounds {n : ℕ} {C δ U : Fin d→ℝ≥0}
    (F : QuantitativeEndpointSkeletonCarrierMaps T m K i n C) {D J : ℝ≥0}
    (H : ∀R,R∈T.cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint m K i R) D J)
    (hδ : ∀j,0<δ j)
    (hlower : ∀R,R∈T.cells → ∀j,R.lower j<R.upper j → δ j≤(R.transverseWidth j).toNNReal)
    (hupper : ∀R,R∈T.cells → ∀j,(R.transverseWidth j).toNNReal≤U j)
    (R : RectangularCell d) (hR : R∈T.cells) (he : R.rank=n) :
    CellCoordinateBounds R (actualQuantitativeExtension F H R hR he).map (nextRankRates δ U C D J i) := by
  intro j z z' heq
  by_cases hi : R.lower i<R.upper i
  · simp only [actualQuantitativeExtension,dif_pos hi]
    let LF := F.toSkeletonCarrierMaps.lowerFamily R he
    have hC : LF.CoordinateBounds C := F.lowerFamily_update_bounds R he
    have hE := LF.relativeCellExtension_coordinate_bounds hR
      (F.toEndpointSkeletonCarrierMaps.lowerFamily_endpoints R he) hi (H R hR hi)
      (LF.prism_path_lipschitz hR hi (C i) (hC i)) (LF.prism_transverse_lipschitz hR C hC)
    have hh := hE j z z' heq
    by_cases hj : R.lower j<R.upper j
    · exact hh.trans (mul_le_mul_of_nonneg_right
        (fillingCoordinateRate_le_nextRankRates R i C δ U D J hδ
          (hlower R hR) (hupper R hR) j hj) (abs_nonneg _))
    · have hz := R.point_eq_of_only_collapsed_coordinate j
        (le_antisymm (R.ordered j) (le_of_not_gt hj)) z z' heq
      rw [hz,dist_self]
      positivity
  · simp only [actualQuantitativeExtension,dif_neg hi]
    exact (F.toSkeletonCarrierMaps.lowerFamily R he).collapsedCellExtension_coordinate_bounds hR
      (F.toEndpointSkeletonCarrierMaps.lowerFamily_endpoints R he) _ _ j z z' heq

def actualQuantitativeNext {n : ℕ} (δ U : Fin d→ℝ≥0) (D J : ℝ≥0)
    (hδ : ∀j,0<δ j)
    (hlower : ∀R,R∈T.cells → ∀j,R.lower j<R.upper j → δ j≤(R.transverseWidth j).toNNReal)
    (hupper : ∀R,R∈T.cells → ∀j,(R.transverseWidth j).toNNReal≤U j)
    (H : ∀R,R∈T.cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint m K i R) D J)
    (F : QuantitativeEndpointSkeletonCarrierMaps T m K i n (atlasRankRates δ U D J i n)) :
    QuantitativeEndpointSkeletonCarrierMaps T m K i (n+1) (atlasRankRates δ U D J i (n+1)) :=
  F.next (actualQuantitativeExtension F H) (atlasRankRates_step_mono δ U D J i n)
    (actualQuantitativeExtension_bounds F H hδ hlower hupper)

def actualQuantitativeSkeleton (δ U : Fin d→ℝ≥0) (D J : ℝ≥0)
    (hδ : ∀j,0<δ j)
    (hlower : ∀R,R∈T.cells → ∀j,R.lower j<R.upper j → δ j≤(R.transverseWidth j).toNNReal)
    (hupper : ∀R,R∈T.cells → ∀j,(R.transverseWidth j).toNNReal≤U j)
    (H : ∀R,R∈T.cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint m K i R) D J) :
    ∀ n,QuantitativeEndpointSkeletonCarrierMaps T m K i n (atlasRankRates δ U D J i n)
  | 0 => QuantitativeEndpointSkeletonCarrierMaps.empty
  | n+1 => actualQuantitativeNext δ U D J hδ hlower hupper H
      (actualQuantitativeSkeleton δ U D J hδ hlower hupper H n)

end
end AbelianTargets


