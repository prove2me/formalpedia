-- Prove2me | solution 1 for AbelianTargets.SkeletonCarrierMaps.projectedMap_translate_of_cell_maps
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:01:38.745967+00:00
-- url     : https://prove2.me/submissions/43cd7341-0148-418a-9e59-766337a0fd0b

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasRankRecursion
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierIntervalInclusion
import Definitions.Def_AT260939824_CarrierProjectionGluing
import Definitions.Def_AT260939824_CarrierProjectionNaturality
import Definitions.Def_AT260939824_CarrierSupportProjection
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
import Definitions.Def_AT260939824_FiniteRectangleIntersections
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntegerGridIntervals
import Definitions.Def_AT260939824_IntegerPrismChart
import Definitions.Def_AT260939824_IntegerPrismTranslation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerPriorities
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AT260939824_OrbitMarkerCuts
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_ParitySwapGeometry
import Definitions.Def_AT260939824_PriorityCuts
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ProbabilityParameters
import Definitions.Def_AT260939824_ProjectedAtlasMaps
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
import Theorems.Thm_AbelianTargets_SupportTorsionData_carrierProjection_push_same
import Theorems.Thm_AbelianTargets_SupportTorsionData_carrierProjection_translate

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.CarrierProjectionNaturality
section
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





theorem carrierProjection_intervalInclusion {K : ℕ} {A B C E : ℤ}
    (hAC : A ≤ C) (hEB : E ≤ B) (p : Realization (2*D.power+1) K C E) :
    D.carrierProjection K A B (intervalInclusion hAC hEB p)=D.carrierProjection K C E p :=
  D.carrierProjection_push_same (intervalVertexInclusion hAC hEB) (fun _ => rfl)
    (carrierCells_mono hAC hEB) (intervalInclusion hAC hEB) (fun _ => rfl) p





end SupportTorsionData
end
end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.ProjectedAtlasMaps
section
/-! Actual global support maps from compatible carrier maps on a rectangular atlas. -/
namespace AbelianTargets
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace RectangularCell

end RectangularCell

namespace SkeletonCarrierMaps
variable {d:ℕ} {K₀:Fin d→ℕ} {T:IntegerRectangularTiling d K₀}
variable {W:Type*} [Fintype W] {H:SimpleGraph W} (D:SupportTorsionData H)
variable {K:ℕ} {i:Fin d} (F:SkeletonCarrierMaps T (2*D.power+1) K i (d+1))



theorem cellProjection_include {P Q:RectangularCell d} (hsub:P.closedBox⊆Q.closedBox)
    (p:CellIntervalCarrier (2*D.power+1) K i P) :
    D.carrierProjection K (Q.lower i) (Q.upper i) (cellIntervalInclude i hsub p)=
      D.carrierProjection K (P.lower i) (P.upper i) p :=
  D.carrierProjection_intervalInclusion
    ((RectangularCell.closedBox_subset_iff P Q).mp hsub i).1
    ((RectangularCell.closedBox_subset_iff P Q).mp hsub i).2 p

theorem projectedMap_eq_cell (R:RectangularCell d) (hR:R∈T.cells)
    (z:RealCoordinates d) (hz:z∈R.closedBox) :
    F.projectedMap D z=D.carrierProjection K (R.lower i) (R.upper i)
      (F.map R hR R.rank_lt_succ_dimension ⟨z,hz⟩) := by
  let P := T.pointCell z
  have hP : P∈T.cells := ⟨z,rfl⟩
  have hsub : P.closedBox⊆R.closedBox := T.pointCell_subset_cell hR hz
  let zP : CellClosedDomain P :=
    ⟨z,P.relativeInterior_subset (T.mem_relativeInterior_pointCell z)⟩
  change D.carrierProjection K (P.lower i) (P.upper i)
    (F.map P hP P.rank_lt_succ_dimension zP)=_
  rw [←cellProjection_include D hsub (F.map P hP P.rank_lt_succ_dimension zP),
    F.compatible P R hP hR P.rank_lt_succ_dimension R.rank_lt_succ_dimension hsub zP]









end SkeletonCarrierMaps
end
end AbelianTargets

end

/-! Literal covariance of the global projected map follows from cell-map covariance. -/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace AbelianTargets.SkeletonCarrierMaps
end AbelianTargets.SkeletonCarrierMaps
open AbelianTargets
open AbelianTargets.SkeletonCarrierMaps
variable {d:ℕ} {K₀ K₁:Fin d→ℕ}
variable {T:IntegerRectangularTiling d K₀} {U:IntegerRectangularTiling d K₁}
variable {W:Type*} [Fintype W] {H:SimpleGraph W} (D:SupportTorsionData H)
variable {K:ℕ} {i:Fin d}
variable (F:SkeletonCarrierMaps T (2*D.power+1) K i (d+1))

theorem solution
    (G:SkeletonCarrierMaps U (2*D.power+1) K i (d+1)) (a:Fin d→ℤ)
    (hcell:∀R:RectangularCell d,R∈T.cells→R.translate a∈U.cells)
    (hmap:∀(R:RectangularCell d)(hR:R∈T.cells)(z:CellClosedDomain R),
      G.map (R.translate a) (hcell R hR) (R.translate a).rank_lt_succ_dimension
        (R.translateClosedPoint a z)=
          IntervalCarriers.realizationTranslation (a i)
            (F.map R hR R.rank_lt_succ_dimension z)) (z:RealCoordinates d) :
    G.projectedMap D (translateCoordinates a z)=
      SupportPair.paritySwap H (a i) (F.projectedMap D z) := by
  let R := T.pointCell z
  have hR : R∈T.cells := ⟨z,rfl⟩
  have hz : z∈R.closedBox := R.relativeInterior_subset (T.mem_relativeInterior_pointCell z)
  have hza : translateCoordinates a z∈(R.translate a).closedBox :=
    (R.mem_closedBox_translateCoordinates a z).mpr hz
  rw [G.projectedMap_eq_cell D (R.translate a) (hcell R hR) _ hza]
  have htrans := hmap R hR ⟨z,hz⟩
  change G.map (R.translate a) (hcell R hR) (R.translate a).rank_lt_succ_dimension
    ⟨translateCoordinates a z,hza⟩=IntervalCarriers.realizationTranslation (a i)
      (F.map R hR R.rank_lt_succ_dimension ⟨z,hz⟩) at htrans
  rw [htrans]
  change D.carrierProjection K (R.lower i+a i) (R.upper i+a i)
      (IntervalCarriers.realizationTranslation (a i) (F.map R hR R.rank_lt_succ_dimension ⟨z,hz⟩))=_
  rw [D.carrierProjection_translate,←F.projectedMap_eq_cell D R hR z hz]
