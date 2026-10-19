-- Prove2me | solution 1 for AbelianTargets.actualQuantitativeExtension_translate
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:01:36.565695+00:00
-- url     : https://prove2.me/submissions/9881e586-c5ec-4e3f-8f66-804a68cf14ca

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoundaryTranslation
import Definitions.Def_AT260939824_AtlasBoundaryTransverseBounds
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasCarrierEndpoints
import Definitions.Def_AT260939824_AtlasControlledCellExtension
import Definitions.Def_AT260939824_AtlasEndpointRecursion
import Definitions.Def_AT260939824_AtlasQuantitativeRecursion
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
import Definitions.Def_AT260939824_CarrierTranslationEquiv
import Definitions.Def_AT260939824_CarrierTranslationGeometry
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ConeDomainNaturality
import Definitions.Def_AT260939824_ContinuousAtlasPatterns
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_ControlledCone
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_DeterministicQuantitativeAtlas
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
import Definitions.Def_AT260939824_RelativeContractionNaturality
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
import Mathlib.Analysis.Normed.Operator.LinearIsometry
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
import Theorems.Thm_AbelianTargets_LowerCellCarrierMaps_boundaryValue_translate
import Theorems.Thm_AbelianTargets_PrismBoundaryData_fill_translate_of_maps

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.AtlasBoundaryTranslation
section
namespace AbelianTargets
noncomputable section
variable {d : ℕ} {m K : ℕ} {i : Fin d}









theorem cellLeftPoint_translate (i : Fin d) (a : Fin d→ℤ) (R : RectangularCell d) :
    cellIntervalTranslate i a R (cellLeftPoint m K i R)=cellLeftPoint m K i (R.translate a) := by
  apply Subtype.ext
  change Probability.push _ (Probability.dirac _)=Probability.dirac _
  rw [Probability.push_dirac]
  rfl

theorem cellRightPoint_translate (i : Fin d) (a : Fin d→ℤ) (R : RectangularCell d) :
    cellIntervalTranslate i a R (cellRightPoint m K i R)=cellRightPoint m K i (R.translate a) := by
  apply Subtype.ext
  change Probability.push _ (Probability.dirac _)=Probability.dirac _
  rw [Probability.push_dirac]
  rfl

namespace IntegerRectangularTiling
variable {K₀ : Fin d→ℕ} (T : IntegerRectangularTiling d K₀)



end IntegerRectangularTiling

namespace LowerCellCarrierMaps
variable {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀} {R : RectangularCell d}



end LowerCellCarrierMaps
end
end AbelianTargets

end

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
open scoped NNReal unitInterval
variable {d : ℕ} {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K n : ℕ} {i : Fin d} {C C' : Fin d→ℝ≥0} {D J : ℝ≥0}

theorem solution
    (F : QuantitativeEndpointSkeletonCarrierMaps T m K i n C) (a : Fin d→ℤ)
    (G : QuantitativeEndpointSkeletonCarrierMaps (T.translate a) m K i n C')
    (H : ∀R,R∈T.cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint m K i R) D J)
    (H' : ∀R,R∈(T.translate a).cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint m K i R) D J)
    (hold : SkeletonCarrierMaps.TranslationCovariant F.toSkeletonCarrierMaps G.toSkeletonCarrierMaps a
      (fun R hR=>T.cell_translate hR a))
    (hH : ∀ (R : RectangularCell d) (hR : R∈T.cells) (hi : R.lower i<R.upper i)
      (p : CellIntervalCarrier m K i R) (t : I),
      (H' (R.translate a) (T.cell_translate hR a) (by simpa [RectangularCell.translate] using hi)).map
        (cellIntervalTranslate i a R p,t)=cellIntervalTranslate i a R ((H R hR hi).map (p,t)))
    (R : RectangularCell d) (hR : R∈T.cells) (he : R.rank=n) (z : CellClosedDomain R) :
    (actualQuantitativeExtension G H' (R.translate a) (T.cell_translate hR a)
      (by simpa only [RectangularCell.rank_translate] using he)).map (R.translateClosedPoint a z)=
      cellIntervalTranslate i a R ((actualQuantitativeExtension F H R hR he).map z) := by
  have he' : (R.translate a).rank=n := by simpa only [RectangularCell.rank_translate] using he
  by_cases hi : R.lower i<R.upper i
  · have hi' : (R.translate a).lower i<(R.translate a).upper i := by simpa [RectangularCell.translate] using hi
    simp only [actualQuantitativeExtension,dif_pos hi,dif_pos hi']
    let LF := F.toSkeletonCarrierMaps.lowerFamily R he
    let LG := G.toSkeletonCarrierMaps.lowerFamily (R.translate a) he'
    let PF := LF.controlledPrismData hR (F.toEndpointSkeletonCarrierMaps.lowerFamily_endpoints R he)
      C (F.lowerFamily_update_bounds R he) hi
    let PG := LG.controlledPrismData (T.cell_translate hR a)
      (G.toEndpointSkeletonCarrierMaps.lowerFamily_endpoints (R.translate a) he')
      C' (G.lowerFamily_update_bounds (R.translate a) he') hi'
    exact PF.fill_translate_of_maps (H R hR hi) a
      (IntervalCarriers.realizationTranslationEquiv (a i)) PG
      (H' (R.translate a) (T.cell_translate hR a) hi')
      (cellLeftPoint_translate i a R) (cellRightPoint_translate i a R)
      (hH R hR hi)
      (LF.boundaryValue_translate hR a LG (by
        intro Q hQ hrQ zQ
        exact hold Q hQ (by omega) zQ)) hi z
  · have hi' : ¬(R.translate a).lower i<(R.translate a).upper i := by simpa [RectangularCell.translate] using hi
    simp only [actualQuantitativeExtension,dif_neg hi,dif_neg hi']
    exact (cellLeftPoint_translate i a R).symm
