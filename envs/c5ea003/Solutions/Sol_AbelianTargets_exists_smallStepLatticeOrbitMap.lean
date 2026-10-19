-- Prove2me | solution 1 for AbelianTargets.exists_smallStepLatticeOrbitMap
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:15:45.979796+00:00
-- url     : https://prove2.me/submissions/c2a84662-7553-43a6-abf4-4619dc222022

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_ActualMarkerAtlas
import Definitions.Def_AT260939824_ActualMarkerQuantitativeAtlas
import Definitions.Def_AT260939824_ActualProjectedOriginLocality
import Definitions.Def_AT260939824_ActualQuantitativeAtlasRecursion
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasCanonicalContractions
import Definitions.Def_AT260939824_AtlasCarrierEndpoints
import Definitions.Def_AT260939824_AtlasEndpointRecursion
import Definitions.Def_AT260939824_AtlasQuantitativeRecursion
import Definitions.Def_AT260939824_AtlasRankRecursion
import Definitions.Def_AT260939824_AtlasRelativeCellExtension
import Definitions.Def_AT260939824_AtlasScaleParameters
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CanonicalActionCovariance
import Definitions.Def_AT260939824_CanonicalIntervalContractions
import Definitions.Def_AT260939824_CanonicalMarkerQuantitativeAtlas
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
import Definitions.Def_AT260939824_DeterministicQuantitativeAtlas
import Definitions.Def_AT260939824_DigitBottomCombing
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_DoubleCoverLifts
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FiniteAtlasDependencyPatterns
import Definitions.Def_AT260939824_FiniteRectangleIntersections
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntegerGridIntervals
import Definitions.Def_AT260939824_IntegerPrismChart
import Definitions.Def_AT260939824_IntegerPrismFilling
import Definitions.Def_AT260939824_IntegerPrismTranslation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_JointCarrierRows
import Definitions.Def_AT260939824_LowerCarrierCollapse
import Definitions.Def_AT260939824_MarkerAtlasQuantitativeWidths
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerPriorities
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AT260939824_OneHeightDeformation
import Definitions.Def_AT260939824_OrbitMarkerCuts
import Definitions.Def_AT260939824_ParallelCollapse
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_ParitySwapGeometry
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
import Definitions.Def_AT260939824_RectangularLocalFiniteness
import Definitions.Def_AT260939824_RectangularTranslation
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_RegularAnisotropicAtlas
import Definitions.Def_AT260939824_RelativeContractionNaturality
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SegmentedOddPath
import Definitions.Def_AT260939824_SimplicialChartGluing
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SmallStepProjectedOrbitMaps
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_SupportPathClasses
import Definitions.Def_AT260939824_SupportWitness
import Definitions.Def_AT260939824_TopologicalWalks
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
import Theorems.Thm_AbelianTargets_ContinuousMarkerBoxes_canonicalProjectedMap_repoint
import Theorems.Thm_AbelianTargets_ContinuousMarkerBoxes_retainedTiles_eventually_eq
import Theorems.Thm_AbelianTargets_QuantitativeEndpointSkeletonCarrierMaps_projected_lattice_step_close
import Theorems.Thm_AbelianTargets_RectangularCell_subcell_mem_dependencyUniverse
import Theorems.Thm_AbelianTargets_SupportTorsionData_carrierProjection_push_same
import Theorems.Thm_AbelianTargets_SupportTorsionData_carrierProjection_uniform_modulus
import Theorems.Thm_AbelianTargets_actualQuantitativeSkeleton_locality
import Theorems.Thm_AbelianTargets_exists_anisotropicClopenMarkers
import Theorems.Thm_AbelianTargets_exists_continuous_markerPriorities
import Theorems.Thm_AbelianTargets_exists_smallAtlasParameters

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.ContinuousMarkerBoxes
section
/-!
# Actual continuous covariant marker boxes

This record contains cut data, rather than a tiling or an assumed atlas.
Its existence follows from the checked finite-priority construction on
the actual marker graph. It supplies all inputs to retained subdivisions.
-/

namespace AbelianTargets
noncomputable section

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]









/-- All continuous covariant cut data exist on an actual free action.
No geometric atlas or continuity conclusion is supplied as an input. -/
theorem exists_continuousMarkerBoxes
    [T1Space X] [SecondCountableTopology X]
    (M : AnisotropicClopenMarkers d L X) (hL : ∀ i,1 ≤ L i) (S : ℕ)
    (free : IsFree (G := Lattice d) (X := X)) (zeroDim : ZeroDimensional X)
    (hscale : ∀ i,32*((2*S+1)^d) ≤ L i) : Nonempty (ContinuousMarkerBoxes M S) := by
  obtain ⟨c,hc,hproper⟩ := exists_continuous_markerPriorities M hL S zeroDim free
  exact ⟨markerBoxesFromPriorities M hL S free c hc hproper hscale⟩

end
end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.ContinuousAtlasStrata
section
/-! The actual incident tile lists and point cells are locally constant in
the action point. The proof uses the finite universe of bounded integer
rectangles near the fixed spatial point, rather than assuming atlas locality. -/

namespace AbelianTargets
noncomputable section
open Filter Topology

namespace IntegerRectangularTiling
variable {d : ℕ} {K : Fin d → ℕ}

theorem pointCell_eq_of_incidentFinset_eq (T U : IntegerRectangularTiling d K)
    (z : RealCoordinates d) (he : T.incidentFinset z = U.incidentFinset z) :
    T.pointCell z = U.pointCell z := by
  apply RectangularCell.closedBox_injective
  ext w
  rw [T.mem_pointCell,U.mem_pointCell]
  constructor
  · intro h R hR hzR
    have hr : R ∈ T.incidentFinset z := by
      rw [he]
      exact (U.mem_incidentFinset z R).mpr ⟨hR,hzR⟩
    exact h R ((T.mem_incidentFinset z R).mp hr).1 hzR
  · intro h R hR hzR
    have hr : R ∈ U.incidentFinset z := by
      rw [← he]
      exact (T.mem_incidentFinset z R).mpr ⟨hR,hzR⟩
    exact h R ((U.mem_incidentFinset z R).mp hr).1 hzR

theorem cell_iff_pointCell_at_interior (T : IntegerRectangularTiling d K)
    (R : RectangularCell d) (z : RealCoordinates d) (hz : z ∈ R.relativeInterior) :
    R ∈ T.cells ↔ T.pointCell z = R := by
  constructor
  · rintro ⟨x,rfl⟩
    exact T.pointCell_constant x z hz
  · intro he
    exact ⟨z,he⟩

variable {Y : Type*} [TopologicalSpace Y]

theorem incidentFinset_eventually_eq (T : Y → IntegerRectangularTiling d K)
    (hlocal : ∀ R x,∀ᶠ y in 𝓝 x,R ∈ (T y).tiles ↔ R ∈ (T x).tiles)
    (x : Y) (z : RealCoordinates d) :
    ∀ᶠ y in 𝓝 x,(T y).incidentFinset z = (T x).incidentFinset z := by
  let F := (RectangularCell.finite_meeting_ball K z).toFinset
  have h : ∀ᶠ y in 𝓝 x,∀ R ∈ F,R ∈ (T y).tiles ↔ R ∈ (T x).tiles := by
    apply (Filter.eventually_all_finset _).mpr
    intro R hR
    exact hlocal R x
  filter_upwards [h] with y hy
  ext R
  rw [(T y).mem_incidentFinset,(T x).mem_incidentFinset]
  constructor
  · rintro ⟨hR,hzR⟩
    have hf : R ∈ F := (Set.Finite.mem_toFinset _).mpr
      ⟨(T y).bounded R hR,z,hzR,Metric.mem_ball_self (by norm_num)⟩
    exact ⟨(hy R hf).mp hR,hzR⟩
  · rintro ⟨hR,hzR⟩
    have hf : R ∈ F := (Set.Finite.mem_toFinset _).mpr
      ⟨(T x).bounded R hR,z,hzR,Metric.mem_ball_self (by norm_num)⟩
    exact ⟨(hy R hf).mpr hR,hzR⟩

theorem pointCell_isLocallyConstant (T : Y → IntegerRectangularTiling d K)
    (hlocal : ∀ R x,∀ᶠ y in 𝓝 x,R ∈ (T y).tiles ↔ R ∈ (T x).tiles)
    (z : RealCoordinates d) : IsLocallyConstant (fun x => (T x).pointCell z) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  filter_upwards [incidentFinset_eventually_eq T hlocal x z] with y hy
  exact (T y).pointCell_eq_of_incidentFinset_eq (T x) z hy

theorem cells_eventually_eq (T : Y → IntegerRectangularTiling d K)
    (hlocal : ∀ R x,∀ᶠ y in 𝓝 x,R ∈ (T y).tiles ↔ R ∈ (T x).tiles)
    (R : RectangularCell d) (x : Y) :
    ∀ᶠ y in 𝓝 x,R ∈ (T y).cells ↔ R ∈ (T x).cells := by
  obtain ⟨z,hz⟩ := R.relativeInterior_nonempty
  filter_upwards [(pointCell_isLocallyConstant T hlocal z).eventually_eq x] with y hy
  rw [(T y).cell_iff_pointCell_at_interior R z hz,
    (T x).cell_iff_pointCell_at_interior R z hz,hy]

theorem finite_cells_eventually_eq (T : Y → IntegerRectangularTiling d K)
    (hlocal : ∀ R x,∀ᶠ y in 𝓝 x,R ∈ (T y).tiles ↔ R ∈ (T x).tiles)
    (F : Finset (RectangularCell d)) (x : Y) :
    ∀ᶠ y in 𝓝 x,∀ R ∈ F,R ∈ (T y).cells ↔ R ∈ (T x).cells :=
  (Filter.eventually_all_finset _).mpr (fun R _ => cells_eventually_eq T hlocal R x)

end IntegerRectangularTiling

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M : AnisotropicClopenMarkers d L X} {S : ℕ}





end
end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.FiniteAtlasDependencyPatterns
section
/-! A finite atlas pattern containing every boundary dependency of every
cell through a fixed spatial point. The universe includes all subcells,
even when their boundary is far from the fixed point. -/

namespace AbelianTargets
noncomputable section
open Filter Topology
namespace RectangularCell
variable {d : ℕ}





end RectangularCell
namespace IntegerRectangularTiling
variable {d : ℕ} {K : Fin d→ℕ}





theorem dependencyPattern_isLocallyConstant {Y : Type*} [TopologicalSpace Y]
    (T : Y→IntegerRectangularTiling d K)
    (hlocal : ∀ R x,∀ᶠ y in 𝓝 x,R∈(T y).tiles ↔ R∈(T x).tiles)
    (z : RealCoordinates d) : IsLocallyConstant (fun x=>(T x).dependencyPattern z) := by
  classical
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  filter_upwards [finite_cells_eventually_eq T hlocal (RectangularCell.dependencyUniverse K z) x]
    with y hy
  exact Finset.filter_congr hy

theorem dependencyPattern_finite_range {Y : Type*} (T : Y→IntegerRectangularTiling d K)
    (z : RealCoordinates d) : (Set.range (fun x=>(T x).dependencyPattern z)).Finite := by
  classical
  apply (RectangularCell.dependencyUniverse K z).powerset.finite_toSet.subset
  rintro _ ⟨x,rfl⟩
  exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)





end IntegerRectangularTiling
end
end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.AtlasDependencyAgreement
section
/-! Equality of the finite dependency pattern determines the point cell
and every cell contained in a parent through the evaluation point. -/

namespace AbelianTargets.IntegerRectangularTiling
noncomputable section
variable {d : ℕ} {K : Fin d→ℕ}

theorem dependencyPattern_eq_contained_cells (T U : IntegerRectangularTiling d K)
    (z : RealCoordinates d) (hpat : T.dependencyPattern z=U.dependencyPattern z)
    (P : RectangularCell d) (hP : P∈T.cells) (hz : z∈P.closedBox)
    (Q : RectangularCell d) (hQP : Q.closedBox⊆P.closedBox) :
    Q∈T.cells ↔ Q∈U.cells := by
  classical
  have hQ := RectangularCell.subcell_mem_dependencyUniverse K z P Q
    (T.cells_bounded hP) hz hQP
  have hh := congrArg (fun s : Finset (RectangularCell d)=>Q∈s) hpat
  exact Iff.of_eq (by simpa only [dependencyPattern,Finset.mem_filter,hQ,true_and] using hh)



end
end AbelianTargets.IntegerRectangularTiling

end

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

-- Preserved source skeleton: AbelianTargets.RegularAnisotropicAtlas
section
/-! An actual regular anisotropic atlas package. Its fields are marker and
cut data; all tiling, stratum, boundary, covariance and locality properties
are theorems about the constructed rectangles. -/

namespace AbelianTargets
noncomputable section
variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]



theorem exists_regularAnisotropicAtlas [T1Space X] [SecondCountableTopology X]
    (L : Fin d → ℕ) (zeroDim : ZeroDimensional X)
    (free : IsFree (G := Lattice d) (X := X))
    (hscale : ∀ i,32*(61^d) ≤ L i) : Nonempty (RegularAnisotropicAtlas L X) := by
  obtain ⟨M⟩ := exists_anisotropicClopenMarkers L zeroDim free
  have hL : ∀ i,1 ≤ L i := by
    intro i
    have hp : 1 ≤ 61^d := Nat.one_le_pow _ _ (by norm_num)
    have hs := hscale i
    omega
  obtain ⟨B⟩ := exists_continuousMarkerBoxes M hL 30 free zeroDim hscale
  exact ⟨⟨M,B⟩⟩

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

-- Preserved source skeleton: AbelianTargets.ActualProjectedOriginLocality
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace AbelianTargets
noncomputable section
open scoped NNReal
variable {d : ℕ} {K₀ : Fin d→ℕ} {T U : IntegerRectangularTiling d K₀}
variable {W : Type*} [Fintype W] {G : SimpleGraph W} (D₀ : SupportTorsionData G)
variable {K : ℕ} {i : Fin d}

theorem actualQuantitativeSkeleton_projected_pattern
    (δ V : Fin d→ℝ≥0) (D J : ℝ≥0) (hδ : ∀j,0<δ j)
    (hlower : ∀R,R∈T.cells → ∀j,R.lower j<R.upper j → δ j≤(R.transverseWidth j).toNNReal)
    (hupper : ∀R,R∈T.cells → ∀j,(R.transverseWidth j).toNNReal≤V j)
    (hlower' : ∀R,R∈U.cells → ∀j,R.lower j<R.upper j → δ j≤(R.transverseWidth j).toNNReal)
    (hupper' : ∀R,R∈U.cells → ∀j,(R.transverseWidth j).toNNReal≤V j)
    (H : ∀R,R∈T.cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint (2*D₀.power+1) K i R) D J)
    (H' : ∀R,R∈U.cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint (2*D₀.power+1) K i R) D J)
    (hH : ∀Q (hQ : Q∈T.cells) (hQ' : Q∈U.cells) (hi : Q.lower i<Q.upper i),H Q hQ hi=H' Q hQ' hi)
    (z : RealCoordinates d) (hpat : T.dependencyPattern z=U.dependencyPattern z) :
    (actualQuantitativeSkeleton δ V D J hδ hlower hupper H (d+1)).toSkeletonCarrierMaps.projectedMap D₀ z=
      (actualQuantitativeSkeleton δ V D J hδ hlower' hupper' H' (d+1)).toSkeletonCarrierMaps.projectedMap D₀ z := by
  let P := T.pointCell z
  have hP : P∈T.cells := ⟨z,rfl⟩
  have hz : z∈P.closedBox := P.relativeInterior_subset (T.mem_relativeInterior_pointCell z)
  have hcells := T.dependencyPattern_eq_contained_cells U z hpat P hP hz
  have hP' : P∈U.cells := (hcells P Set.Subset.rfl).mp hP
  rw [SkeletonCarrierMaps.projectedMap_eq_cell D₀ _ P hP z hz,
    SkeletonCarrierMaps.projectedMap_eq_cell D₀ _ P hP' z hz]
  apply congrArg (D₀.carrierProjection K (P.lower i) (P.upper i))
  exact actualQuantitativeSkeleton_locality δ V D J hδ hlower hupper hlower' hupper' H H' P
    hcells (fun Q hQ hQ' hi _=>hH Q hQ hQ' hi) (d+1) P hP hP' P.rank_lt_succ_dimension Set.Subset.rfl ⟨z,hz⟩

variable {L : Fin d→ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M₀ : AnisotropicClopenMarkers d L X} {S : ℕ}



theorem ContinuousMarkerBoxes.canonicalProjectedMap_pattern
    (B : ContinuousMarkerBoxes M₀ S) (hL : ∀j,1≤L j) (hS : 24≤S)
    (K : ℕ) (i : Fin d) (J : ℝ≥0)
    (H : IntervalCarriers.NormalizedContractionFamily (2*D₀.power+1) K (6*L i) J)
    (x y : X) (z : RealCoordinates d)
    (hpat : (B.tiling hL (by omega) x).dependencyPattern z=(B.tiling hL (by omega) y).dependencyPattern z) :
    B.canonicalProjectedMap D₀ hL hS K i J H x z=B.canonicalProjectedMap D₀ hL hS K i J H y z := by
  unfold canonicalProjectedMap canonicalQuantitativeSkeleton quantitativeSkeleton
  apply actualQuantitativeSkeleton_projected_pattern
  · intro Q hQ hQ' hi
    rfl
  · exact hpat

end
end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.FinitePatternFunctions
section
/-! A function determined by a locally constant finite pattern is itself
locally constant and has finite range. This is the action-parameter step
used after proving literal recursive dependence on the atlas pattern. -/

namespace AbelianTargets
noncomputable section
open Filter Topology

theorem locallyConstant_of_pattern {X P Y : Type*} [TopologicalSpace X]
    (p : X→P) (hp : IsLocallyConstant p) (f : X→Y)
    (hdepends : ∀x y,p x=p y → f x=f y) : IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  filter_upwards [hp.eventually_eq x] with y hy
  exact hdepends y x hy

theorem finite_range_of_constant_pattern {X P Y : Type*}
    (p : X→P) (hp : (Set.range p).Finite) (f : X→Y)
    (hdepends : ∀x y,p x=p y → f x=f y) : (Set.range f).Finite := by
  classical
  let g : Set.range p→Y := fun a=>f a.property.choose
  letI : Finite (Set.range p) := hp.to_subtype
  apply (Set.finite_range g).subset
  rintro _ ⟨x,rfl⟩
  let a : Set.range p := ⟨p x,⟨x,rfl⟩⟩
  exact ⟨a,hdepends a.property.choose x a.property.choose_spec⟩

end
end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.CanonicalProjectedOrigin
section
namespace AbelianTargets
noncomputable section
open scoped NNReal
variable {d : ℕ} {L : Fin d→ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M₀ : AnisotropicClopenMarkers d L X} {S : ℕ}
variable {W : Type*} [Fintype W] {G : SimpleGraph W} (D₀ : SupportTorsionData G)

theorem ContinuousMarkerBoxes.canonicalProjectedMap_isLocallyConstant
    (B : ContinuousMarkerBoxes M₀ S) (hL : ∀j,1≤L j) (hS : 24≤S)
    (K : ℕ) (i : Fin d) (J : ℝ≥0)
    (H : IntervalCarriers.NormalizedContractionFamily (2*D₀.power+1) K (6*L i) J)
    (z : RealCoordinates d) : IsLocallyConstant (fun x=>B.canonicalProjectedMap D₀ hL hS K i J H x z) := by
  apply locallyConstant_of_pattern (fun x=>(B.tiling hL (by omega) x).dependencyPattern z)
    (IntegerRectangularTiling.dependencyPattern_isLocallyConstant
      (B.tiling hL (by omega)) B.retainedTiles_eventually_eq z)
  intro x y hpat
  exact B.canonicalProjectedMap_pattern D₀ hL hS K i J H x y z hpat

theorem ContinuousMarkerBoxes.canonicalProjectedMap_finite_range
    (B : ContinuousMarkerBoxes M₀ S) (hL : ∀j,1≤L j) (hS : 24≤S)
    (K : ℕ) (i : Fin d) (J : ℝ≥0)
    (H : IntervalCarriers.NormalizedContractionFamily (2*D₀.power+1) K (6*L i) J)
    (z : RealCoordinates d) : (Set.range (fun x=>B.canonicalProjectedMap D₀ hL hS K i J H x z)).Finite := by
  apply finite_range_of_constant_pattern (fun x=>(B.tiling hL (by omega) x).dependencyPattern z)
    (IntegerRectangularTiling.dependencyPattern_finite_range (B.tiling hL (by omega)) z)
  intro x y hpat
  exact B.canonicalProjectedMap_pattern D₀ hL hS K i J H x y z hpat

theorem ContinuousMarkerBoxes.continuous_canonicalProjectedMap
    (B : ContinuousMarkerBoxes M₀ S) (hL : ∀j,1≤L j) (hS : 24≤S)
    (K : ℕ) (i : Fin d) (J : ℝ≥0)
    (H : IntervalCarriers.NormalizedContractionFamily (2*D₀.power+1) K (6*L i) J)
    (z : RealCoordinates d) : Continuous (fun x=>B.canonicalProjectedMap D₀ hL hS K i J H x z) :=
  (B.canonicalProjectedMap_isLocallyConstant D₀ hL hS K i J H z).continuous

end
end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.CanonicalActionCovariance
section
/-!
# Action covariance and integer-lattice parity closing

The actual canonical atlas projection commutes with repointing by the lattice
shift and the corresponding support-shore parity. Integer-lattice unit edges
suffice for the final generator comparison after the parity shear.
-/

namespace AbelianTargets
noncomputable section
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000





section Action
variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X]
variable [ContinuousVAdd (Lattice d) X]
variable {M₀ : AnisotropicClopenMarkers d L X} {S : ℕ}
variable {W : Type*} [Fintype W] {G : SimpleGraph W}





/-- The same identity in the orientation used by the parity-map interface. -/
theorem ContinuousMarkerBoxes.canonicalProjectedMap_repoint_forward
    (B : ContinuousMarkerBoxes M₀ S) (D₀ : SupportTorsionData G)
    (hL : ∀ j, 1 ≤ L j) (hS : 24 ≤ S) (K : ℕ) (i : Fin d) (J : ℝ≥0)
    (H : IntervalCarriers.NormalizedContractionFamily
      (2 * D₀.power + 1) K (6 * L i) J)
    (x : X) (t : Lattice d) (z : RealCoordinates d) :
    B.canonicalProjectedMap D₀ hL hS K i J H (t +ᵥ x) z =
      SupportPair.paritySwap G (t i)
        (B.canonicalProjectedMap D₀ hL hS K i J H x (translateCoordinates t z)) := by
  have hh := B.canonicalProjectedMap_repoint D₀ hL hS K i J H x t z
  by_cases ht : t i % 2 = 0
  · simpa [SupportPair.paritySwap, ht] using hh.symm
  · simpa [SupportPair.paritySwap, ht, SupportPair.swap_swap]
      using (congrArg (SupportPair.swap G) hh).symm

end Action






end
end AbelianTargets

namespace AbelianTargets



namespace ParitySheared

variable {d : ℕ} (hd : 1 ≤ d) {X : Type*}





























end ParitySheared
end AbelianTargets

end

/-!
Actual small-step orbit maps for arbitrary free zero-dimensional Polish
lattice actions. All geometric and quantitative parameters are constructed
before the canonical projected map is evaluated on the action space.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem solution
    {d : ℕ} {X V : Type*} [TopologicalSpace X] [PolishSpace X]
    [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
    [Fintype V] {H : SimpleGraph V} (D : SupportTorsionData H) (i : Fin d)
    (zeroDim : ZeroDimensional X) (free : IsFree (G := Lattice d) (X := X))
    {ε : ℝ} (hε : 0 < ε) :
    Nonempty (SmallStepLatticeOrbitMap (X := X) H i ε) := by
  classical
  obtain ⟨δ, hδ, hmod⟩ := D.carrierProjection_uniform_modulus ε hε
  have hm : 2 ≤ 2 * D.power + 1 := by have := D.power_pos; omega
  obtain ⟨P⟩ := exists_smallAtlasParameters (2 * D.power + 1) hm d i hδ
  obtain ⟨A⟩ := exists_regularAnisotropicAtlas P.scales zeroDim free P.scales_large
  let B := A.boxes
  have h30 : (24 : ℕ) ≤ 30 := by norm_num
  have hsmall (j : Fin d) :
      (atlasRankRates
        (fun k => (P.scales k : ℝ≥0) / (32 * ((2 * 30 + 1) ^ d : ℕ)))
        (fun k => 6 * (P.scales k : ℝ≥0))
        (IntervalCarriers.uniformCarrierSpeed (2 * D.power + 1) P.height)
        P.joint i (d + 1) j : ℝ) < δ := by
    simpa only [show 2 * 30 + 1 = (61 : ℕ) by norm_num] using P.rate_lt j
  refine ⟨{
    orbitMap := fun x g => B.canonicalProjectedMap D P.scales_pos h30
      P.height i P.joint P.contractions x (fun k => (g k : ℝ))
    continuous_origin := ?_
    finite_range_origin := ?_
    covariance := ?_
    unit_step := ?_
  }⟩
  · simpa only [Pi.zero_apply, Int.cast_zero] using
      B.continuous_canonicalProjectedMap D P.scales_pos h30
        P.height i P.joint P.contractions (0 : RealCoordinates d)
  · simpa only [Pi.zero_apply, Int.cast_zero] using
      B.canonicalProjectedMap_finite_range D P.scales_pos h30
        P.height i P.joint P.contractions (0 : RealCoordinates d)
  · intro x g
    have hz : translateCoordinates g (0 : RealCoordinates d) =
        (fun k => (g k : ℝ)) := by
      funext k
      simp [translateCoordinates]
    have hh := B.canonicalProjectedMap_repoint_forward D P.scales_pos h30
      P.height i P.joint P.contractions x g (0 : RealCoordinates d)
    rw [hz] at hh
    simpa only [Pi.zero_apply, Int.cast_zero] using hh
  · intro x j g
    have hh :=
      (B.canonicalQuantitativeSkeleton P.scales_pos h30 x
        (2 * D.power + 1) P.height i P.joint P.contractions (d + 1)).projected_lattice_step_close
          D ε δ (fun a b p q hpq => hmod P.height a b p q hpq) j g (hsmall j)
    simpa only [ContinuousMarkerBoxes.canonicalProjectedMap, dist_comm] using hh
