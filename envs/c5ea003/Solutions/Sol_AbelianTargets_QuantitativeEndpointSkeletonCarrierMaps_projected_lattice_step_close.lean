-- Prove2me | solution 1 for AbelianTargets.QuantitativeEndpointSkeletonCarrierMaps.projected_lattice_step_close
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:05:40.693545+00:00
-- url     : https://prove2.me/submissions/b5e40ccd-df10-4956-be62-1c05c4c6396d

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasEndpointRecursion
import Definitions.Def_AT260939824_AtlasQuantitativeRecursion
import Definitions.Def_AT260939824_AtlasRankRecursion
import Definitions.Def_AT260939824_AtlasRelativeCellExtension
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CanonicalActionCovariance
import Definitions.Def_AT260939824_CanonicalIntervalContractions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierControlledContraction
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierHeightChain
import Definitions.Def_AT260939824_CarrierHeightDeformation
import Definitions.Def_AT260939824_CarrierIntervalInclusion
import Definitions.Def_AT260939824_CarrierProjectionGluing
import Definitions.Def_AT260939824_CarrierProjectionNaturality
import Definitions.Def_AT260939824_CarrierSupportProjection
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
import Definitions.Def_AT260939824_DoubleCoverLifts
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FiniteRectangleIntersections
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntegerCellGluing
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
import Definitions.Def_AT260939824_ProbabilityParameters
import Definitions.Def_AT260939824_ProbabilityPushDirac
import Definitions.Def_AT260939824_ProjectedAtlasMaps
import Definitions.Def_AT260939824_RealizedBottomCombing
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
import Definitions.Def_AT260939824_TriangleCollapse
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
import Theorems.Thm_AbelianTargets_SupportTorsionData_carrierProjection_push_same

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





theorem projectedMap_unit_interval_cell (j:Fin d) (z:RealCoordinates d) (n:ℤ)
    (x y:ℝ) (hx:x∈Set.Icc (n:ℝ) ((n:ℝ)+1)) (hy:y∈Set.Icc (n:ℝ) ((n:ℝ)+1)) :
    ∃R:RectangularCell d,∃hR:R∈T.cells,
      ∃hxR:Function.update z j x∈R.closedBox,∃hyR:Function.update z j y∈R.closedBox,
        F.projectedMap D (Function.update z j x)=D.carrierProjection K (R.lower i) (R.upper i)
          (F.map R hR R.rank_lt_succ_dimension ⟨Function.update z j x,hxR⟩) ∧
        F.projectedMap D (Function.update z j y)=D.carrierProjection K (R.lower i) (R.upper i)
          (F.map R hR R.rank_lt_succ_dimension ⟨Function.update z j y,hyR⟩) := by
  let w := Function.update z j ((n:ℝ)+1/2)
  let R := T.pointCell w
  have hR : R∈T.cells := ⟨w,rfl⟩
  have hw : w∈R.closedBox := R.relativeInterior_subset (T.mem_relativeInterior_pointCell w)
  have hxR := R.coordinate_unit_interval z j n hw x hx
  have hyR := R.coordinate_unit_interval z j n hw y hy
  exact ⟨R,hR,hxR,hyR,F.projectedMap_eq_cell D R hR _ hxR,F.projectedMap_eq_cell D R hR _ hyR⟩



end SkeletonCarrierMaps
end
end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.ProjectedAtlasEstimates
section
/-! Coordinate estimates survive the actual carrier projection with its common modulus. -/
namespace AbelianTargets.QuantitativeEndpointSkeletonCarrierMaps
noncomputable section
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
variable {d:ℕ} {K₀:Fin d→ℕ} {T:IntegerRectangularTiling d K₀}
variable {W:Type*} [Fintype W] {H:SimpleGraph W} (D:SupportTorsionData H)
variable {K:ℕ} {i:Fin d} {C:Fin d→ℝ≥0}
variable (F:QuantitativeEndpointSkeletonCarrierMaps T (2*D.power+1) K i (d+1) C)

theorem projected_coordinate_unit_close (ε δ:ℝ)
    (hmod:∀A B:ℤ,∀p q:IntervalCarriers.Realization (2*D.power+1) K A B,
      dist p q<δ→dist (D.carrierProjection K A B p) (D.carrierProjection K A B q)<ε)
    (j:Fin d) (z:RealCoordinates d) (n:ℤ) (x y:ℝ)
    (hx:x∈Set.Icc (n:ℝ) ((n:ℝ)+1)) (hy:y∈Set.Icc (n:ℝ) ((n:ℝ)+1))
    (hsmall:(C j:ℝ)*|x-y|<δ) :
    dist (F.toSkeletonCarrierMaps.projectedMap D (Function.update z j x))
      (F.toSkeletonCarrierMaps.projectedMap D (Function.update z j y))<ε := by
  obtain ⟨R,hR,hxR,hyR,hprojx,hprojy⟩ :=
    F.toSkeletonCarrierMaps.projectedMap_unit_interval_cell D j z n x y hx hy
  rw [hprojx,hprojy]
  apply hmod
  have hb := F.coordinate_bounds R hR R.rank_lt_succ_dimension j
    ⟨Function.update z j x,hxR⟩ ⟨Function.update z j y,hyR⟩
    (by intro k hk; simp only [Function.update_of_ne hk])
  have hb' : dist (F.map R hR R.rank_lt_succ_dimension ⟨Function.update z j x,hxR⟩)
      (F.map R hR R.rank_lt_succ_dimension ⟨Function.update z j y,hyR⟩)≤(C j:ℝ)*|x-y| := by
    simpa using hb
  exact hb'.trans_lt hsmall

theorem projected_integer_step_close (ε δ:ℝ)
    (hmod:∀A B:ℤ,∀p q:IntervalCarriers.Realization (2*D.power+1) K A B,
      dist p q<δ→dist (D.carrierProjection K A B p) (D.carrierProjection K A B q)<ε)
    (j:Fin d) (z:RealCoordinates d) (n:ℤ) (hsmall:(C j:ℝ)<δ) :
    dist (F.toSkeletonCarrierMaps.projectedMap D (Function.update z j (n:ℝ)))
      (F.toSkeletonCarrierMaps.projectedMap D (Function.update z j ((n:ℝ)+1)))<ε := by
  apply F.projected_coordinate_unit_close D ε δ hmod j z n
    (n:ℝ) ((n:ℝ)+1) (by constructor <;> linarith) (by constructor <;> linarith)
  simpa using hsmall

end
end AbelianTargets.QuantitativeEndpointSkeletonCarrierMaps

end

/-!
# Action covariance and integer-lattice parity closing

The actual canonical atlas projection commutes with repointing by the lattice
shift and the corresponding support-shore parity. Integer-lattice unit edges
suffice for the final generator comparison after the parity shear.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open AbelianTargets.QuantitativeEndpointSkeletonCarrierMaps

theorem solution
    {d K : ℕ} {K₀ : Fin d → ℕ} {T : IntegerRectangularTiling d K₀}
    {W : Type*} [Fintype W] {G : SimpleGraph W}
    (D₀ : SupportTorsionData G) {i : Fin d} {C : Fin d → ℝ≥0}
    (F : QuantitativeEndpointSkeletonCarrierMaps T (2 * D₀.power + 1) K i (d + 1) C)
    (ε δ : ℝ)
    (hmod : ∀ A B : ℤ,
      ∀ p q : IntervalCarriers.Realization (2 * D₀.power + 1) K A B,
      dist p q < δ →
        dist (D₀.carrierProjection K A B p) (D₀.carrierProjection K A B q) < ε)
    (j : Fin d) (g : Lattice d) (hsmall : (C j : ℝ) < δ) :
    dist (F.toSkeletonCarrierMaps.projectedMap D₀ (fun k => (g k : ℝ)))
      (F.toSkeletonCarrierMaps.projectedMap D₀
        (fun k => ((g + unitVector j) k : ℝ))) < ε := by
  classical
  have h₀ : Function.update (fun k => (g k : ℝ)) j (g j : ℝ) =
      (fun k => (g k : ℝ)) := by
    funext k
    by_cases hk : k = j <;> simp [Function.update, hk]
  have h₁ : Function.update (fun k => (g k : ℝ)) j ((g j : ℝ) + 1) =
      (fun k => ((g + unitVector j) k : ℝ)) := by
    funext k
    by_cases hk : k = j <;> simp [Function.update, unitVector, hk]
  simpa only [h₀, h₁] using
    F.projected_integer_step_close D₀ ε δ hmod j (fun k => (g k : ℝ)) (g j) hsmall
