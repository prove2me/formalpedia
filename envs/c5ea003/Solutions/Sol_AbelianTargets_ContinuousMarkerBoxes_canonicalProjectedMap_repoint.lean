-- Prove2me | solution 1 for AbelianTargets.ContinuousMarkerBoxes.canonicalProjectedMap_repoint
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:08:17.170126+00:00
-- url     : https://prove2.me/submissions/c8fa46d1-0295-4678-bd49-7f6db743a108

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_ActualMarkerAtlas
import Definitions.Def_AT260939824_ActualMarkerQuantitativeAtlas
import Definitions.Def_AT260939824_ActualProjectedOriginLocality
import Definitions.Def_AT260939824_ActualQuantitativeAtlasRecursion
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoundaryTranslation
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasCanonicalContractions
import Definitions.Def_AT260939824_AtlasCarrierEndpoints
import Definitions.Def_AT260939824_AtlasEndpointRecursion
import Definitions.Def_AT260939824_AtlasQuantitativeRecursion
import Definitions.Def_AT260939824_AtlasRankCovariance
import Definitions.Def_AT260939824_AtlasRankRecursion
import Definitions.Def_AT260939824_AtlasRelativeCellExtension
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
import Definitions.Def_AT260939824_CarrierTranslationGeometry
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_CommonHeightCarrierContraction
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ConeDomainNaturality
import Definitions.Def_AT260939824_ContinuousAtlasPatterns
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_ContinuousOrbitCuts
import Definitions.Def_AT260939824_ControlledCone
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_CovariantOrbitCuts
import Definitions.Def_AT260939824_DeterministicQuantitativeAtlas
import Definitions.Def_AT260939824_DigitBottomCombing
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
import Definitions.Def_AT260939824_RetainedMarkerTiles
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
import Theorems.Thm_AbelianTargets_EndpointSkeletonCarrierMaps_next_translationCovariant
import Theorems.Thm_AbelianTargets_IntervalCarriers_NormalizedContractionFamily_atWidthInterval_shift
import Theorems.Thm_AbelianTargets_SkeletonCarrierMaps_projectedMap_translate_of_cell_maps
import Theorems.Thm_AbelianTargets_actualQuantitativeExtension_translate

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.RetainedTilesCovariance
section
namespace AbelianTargets
noncomputable section
variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M : AnisotropicClopenMarkers d L X} {S : ℕ}

theorem ContinuousMarkerBoxes.cutSide_repoint (B : ContinuousMarkerBoxes M S)
    (x : X) (t a : Lattice d) (i : Fin d) (s : Bool) :
    cutSide (B.cuts (t +ᵥ x) a i) s = cutSide (B.cuts x (a+t) i) s-t i := by
  rw [B.cuts_repoint]
  cases s <;> rfl

theorem ContinuousMarkerBoxes.mem_localCutLevels_iff (B : ContinuousMarkerBoxes M S)
    (x : X) (a : Lattice d) (i : Fin d) (v : ℤ) :
    v ∈ B.localCutLevels x a i ↔
      ∃ b ∈ inactiveOrbitNeighbors M 6 x a,∃ s : Bool,v = cutSide (B.cuts x b i) s := by
  constructor
  · intro hv
    obtain ⟨b,hb,hv⟩ := Finset.mem_biUnion.mp hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with hv | hv
    · exact ⟨b,hb,false,hv⟩
    · exact ⟨b,hb,true,hv⟩
  · rintro ⟨b,hb,s,rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨b,hb,?_⟩
    cases s <;> simp [cutSide]

theorem ContinuousMarkerBoxes.mem_localCutLevels_repoint (B : ContinuousMarkerBoxes M S)
    (x : X) (t a : Lattice d) (i : Fin d) (v : ℤ) :
    v ∈ B.localCutLevels (t +ᵥ x) a i ↔ v+t i ∈ B.localCutLevels x (a+t) i := by
  rw [B.mem_localCutLevels_iff,B.mem_localCutLevels_iff]
  constructor
  · rintro ⟨b,hb,s,hv⟩
    refine ⟨b+t,(mem_inactiveOrbitNeighbors_repoint M 6 x t a b).mp hb,s,?_⟩
    rw [hv,B.cutSide_repoint]
    omega
  · rintro ⟨b,hb,s,hv⟩
    have hb' : b-t ∈ inactiveOrbitNeighbors M 6 (t +ᵥ x) a := by
      apply (mem_inactiveOrbitNeighbors_repoint M 6 x t a (b-t)).mpr
      simpa using hb
    refine ⟨b-t,hb',s,?_⟩
    rw [B.cutSide_repoint]
    simpa using (eq_sub_iff_add_eq.mpr hv)

theorem consecutivePairs_of_shift {D E : Finset ℤ} (t a b : ℤ)
    (hD : ∀ v,v ∈ D ↔ v+t ∈ E) :
    (a,b) ∈ consecutivePairs D ↔ (a+t,b+t) ∈ consecutivePairs E := by
  rw [mem_consecutivePairs,mem_consecutivePairs]
  constructor
  · rintro ⟨ha,hb,hab,hgap⟩
    refine ⟨(hD a).mp ha,(hD b).mp hb,by omega,?_⟩
    intro z hz hzz
    have hzD : z-t ∈ D := (hD (z-t)).mpr (by simpa using hz)
    exact hgap (z-t) hzD ⟨by omega,by omega⟩
  · rintro ⟨ha,hb,hab,hgap⟩
    refine ⟨(hD a).mpr ha,(hD b).mpr hb,by omega,?_⟩
    intro z hz hzz
    exact hgap (z+t) ((hD z).mp hz) ⟨by omega,by omega⟩

theorem ContinuousMarkerBoxes.GridCell_repoint (B : ContinuousMarkerBoxes M S)
    (x : X) (t a : Lattice d) (R : RectangularCell d) :
    B.GridCell (t +ᵥ x) a R ↔ B.GridCell x (a+t) (R.translate t) := by
  constructor <;> intro h i
  · have hi := h i
    refine ⟨(consecutivePairs_of_shift (t i) (R.lower i) (R.upper i)
      (B.mem_localCutLevels_repoint x t a i)).mp hi.1,?_⟩
    have hb := B.cuts_repoint x t a i
    rw [hb] at hi
    change (B.cuts x (a+t) i).1 ≤ R.lower i+t i ∧
      R.upper i+t i ≤ (B.cuts x (a+t) i).2
    exact ⟨by have hh:=hi.2.1; dsimp only at hh; omega,
      by have hh:=hi.2.2; dsimp only at hh; omega⟩
  · have hi := h i
    refine ⟨(consecutivePairs_of_shift (t i) (R.lower i) (R.upper i)
      (B.mem_localCutLevels_repoint x t a i)).mpr hi.1,?_⟩
    rw [B.cuts_repoint]
    change (B.cuts x (a+t) i).1-t i ≤ R.lower i ∧
      R.upper i ≤ (B.cuts x (a+t) i).2-t i
    have hlo := hi.2.1
    have hhi := hi.2.2
    change (B.cuts x (a+t) i).1 ≤ R.lower i+t i at hlo
    change R.upper i+t i ≤ (B.cuts x (a+t) i).2 at hhi
    omega

theorem ContinuousMarkerBoxes.markerBox_repoint (B : ContinuousMarkerBoxes M S)
    (x : X) (t a : Lattice d) :
    (B.markerBox (t +ᵥ x) a).translate t = B.markerBox x (a+t) := by
  apply RectangularCell.endpoint_pair_injective
  apply Prod.ext <;> funext i <;>
    simp [markerBox,RectangularCell.translate,B.cuts_repoint]

theorem disjoint_translated_rectangles (R Q : RectangularCell d) (t : Lattice d) :
    Disjoint (R.translate t).relativeInterior (Q.translate t).closedBox ↔
      Disjoint R.relativeInterior Q.closedBox := by
  constructor
  · intro h
    apply Set.disjoint_left.mpr
    intro z hzR hzQ
    exact Set.disjoint_left.mp h
      ((R.mem_relativeInterior_translate t z).mpr hzR)
      ((Q.mem_closedBox_translateCoordinates t z).mpr hzQ)
  · intro h
    apply Set.disjoint_left.mpr
    intro z hzR hzQ
    have hr : translateCoordinates (-t) z ∈ R.relativeInterior := by
      apply (R.mem_relativeInterior_translate t _).mp
      simpa only [translateCoordinates_cancel_neg] using hzR
    have hq : translateCoordinates (-t) z ∈ Q.closedBox := by
      apply (Q.mem_closedBox_translateCoordinates t _).mp
      simpa only [translateCoordinates_cancel_neg] using hzQ
    exact Set.disjoint_left.mp h hr hq

theorem ContinuousMarkerBoxes.Retained_repoint (B : ContinuousMarkerBoxes M S)
    (x : X) (t a : Lattice d) (R : RectangularCell d) :
    B.Retained (t +ᵥ x) a R ↔ B.Retained x (a+t) (R.translate t) := by
  constructor
  · rintro ⟨ha,hgrid,hkeep⟩
    refine ⟨by simpa only [add_vadd] using ha,(B.GridCell_repoint x t a R).mp hgrid,?_⟩
    intro b hb hp
    have hb' : (b-t) +ᵥ (t +ᵥ x) ∈ M.markers := by
      rw [← add_vadd,sub_add_cancel]
      exact hb
    have hp' : (B.priority (t +ᵥ x) (b-t)).val < (B.priority (t +ᵥ x) a).val := by
      simpa only [B.priority_repoint,sub_add_cancel] using hp
    have hd := (disjoint_translated_rectangles R (B.markerBox (t +ᵥ x) (b-t)) t).mpr
      (hkeep (b-t) hb' hp')
    simpa only [B.markerBox_repoint,sub_add_cancel] using hd
  · rintro ⟨ha,hgrid,hkeep⟩
    refine ⟨by simpa only [add_vadd] using ha,(B.GridCell_repoint x t a R).mpr hgrid,?_⟩
    intro b hb hp
    have hb' : (b+t) +ᵥ x ∈ M.markers := by simpa only [add_vadd] using hb
    have hp' : (B.priority x (b+t)).val < (B.priority x (a+t)).val := by
      simpa only [B.priority_repoint] using hp
    apply (disjoint_translated_rectangles R (B.markerBox (t +ᵥ x) b) t).mp
    simpa only [B.markerBox_repoint] using hkeep (b+t) hb' hp'

theorem ContinuousMarkerBoxes.retainedTiles_repoint (B : ContinuousMarkerBoxes M S)
    (x : X) (t : Lattice d) :
    (fun R : RectangularCell d => R.translate t) '' B.retainedTiles (t +ᵥ x) =
      B.retainedTiles x := by
  ext R
  constructor
  · rintro ⟨Q,⟨a,ha⟩,rfl⟩
    exact ⟨a+t,(B.Retained_repoint x t a Q).mp ha⟩
  · rintro ⟨a,ha⟩
    refine ⟨R.translate (-t),⟨a-t,?_⟩,R.translate_cancel_neg t⟩
    apply (B.Retained_repoint x t (a-t) (R.translate (-t))).mpr
    simpa only [sub_add_cancel,RectangularCell.translate_cancel_neg] using ha

end
end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.AtlasCanonicalContractions
section
/-! One fixed family of contractions at zero-based interval widths gives
a literal contraction provider on all atlas cells, with exact translation
covariance. There is no new choice at a translated cell. -/

namespace AbelianTargets
open scoped unitInterval NNReal
noncomputable section
variable {d m K S : ℕ} {J : ℝ≥0}
variable (H : IntervalCarriers.NormalizedContractionFamily m K S J)

theorem normalizedWidth_map_congr (n n' : ℕ) (he : n=n')
    (hn : 0<n) (hn' : 0<n') (hS : n≤S) (hS' : n'≤S)
    (A B : ℤ) (hb : (n:ℤ)+A=B) (hb' : (n':ℤ)+A=B)
    (p : IntervalCarriers.Realization m K A B) (t : I) :
    (H.atWidthInterval n hn hS A B hb).map (p,t)=
      (H.atWidthInterval n' hn' hS' A B hb').map (p,t) := by
  subst n'
  rfl



theorem canonicalCellContraction_translate (i : Fin d) (R : RectangularCell d)
    (hi : R.lower i<R.upper i) (hS : (R.upper i-R.lower i).toNat≤S)
    (a : Fin d→ℤ) (p : CellIntervalCarrier m K i R) (t : I) :
    (canonicalCellContraction H i (R.translate a) (by dsimp [RectangularCell.translate]; omega)
      (by simpa [RectangularCell.translate] using hS)).map (cellIntervalTranslate i a R p,t)=
      cellIntervalTranslate i a R ((canonicalCellContraction H i R hi hS).map (p,t)) := by
  simp only [canonicalCellContraction,ControlledContraction.rebase_map,
    RectangularCell.translate]
  have hw : R.upper i+a i-(R.lower i+a i)=R.upper i-R.lower i := by omega
  rw [normalizedWidth_map_congr H _ (R.upper i-R.lower i).toNat (congrArg Int.toNat hw)
    _ (by omega) _ hS _ _ _
    (by rw [Int.toNat_of_nonneg (by omega : 0≤R.upper i-R.lower i)]; omega)]
  exact H.atWidthInterval_shift (R.upper i-R.lower i).toNat (by omega) hS
    (R.lower i) (R.upper i) (R.lower i+a i) (R.upper i+a i) (a i)
    (by rw [Int.toNat_of_nonneg (by omega : 0≤R.upper i-R.lower i)] <;> omega) rfl rfl p t



end
end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.AtlasRankCovariance
section
/-! Translation covariance propagates through the literal rank recursion. -/
namespace AbelianTargets
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace SkeletonCarrierMaps
variable {d:ℕ} {K₀ K₁:Fin d→ℕ}
variable {T:IntegerRectangularTiling d K₀} {U:IntegerRectangularTiling d K₁}
variable {m K n:ℕ} {i:Fin d}



theorem empty_translationCovariant (a:Fin d→ℤ)
    (hcell:∀R:RectangularCell d,R∈T.cells→R.translate a∈U.cells) :
    TranslationCovariant (empty:SkeletonCarrierMaps T m K i 0)
      (empty:SkeletonCarrierMaps U m K i 0) a hcell := by
  intro R hR hr z
  exact (Nat.not_lt_zero _ hr).elim

end SkeletonCarrierMaps

namespace EndpointSkeletonCarrierMaps
variable {d:ℕ} {K₀ K₁:Fin d→ℕ}
variable {T:IntegerRectangularTiling d K₀} {U:IntegerRectangularTiling d K₁}
variable {m K n:ℕ} {i:Fin d}
variable (F:EndpointSkeletonCarrierMaps T m K i n) (G:EndpointSkeletonCarrierMaps U m K i n)



end EndpointSkeletonCarrierMaps
end
end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.DeterministicAtlasCovariance
section
/-! The computed quantitative atlas builder preserves a covariant local extension rule. -/
namespace AbelianTargets
noncomputable section
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d:ℕ} {K₀ K₁:Fin d→ℕ}
variable {T:IntegerRectangularTiling d K₀} {V:IntegerRectangularTiling d K₁}
variable {m K:ℕ} {i:Fin d}

theorem actualQuantitativeSkeleton_covariant
    (δ U:Fin d→ℝ≥0) (D J:ℝ≥0) (hδ:∀j,0<δ j)
    (hlT:∀R,R∈T.cells→∀j,R.lower j<R.upper j→δ j≤(R.transverseWidth j).toNNReal)
    (huT:∀R,R∈T.cells→∀j,(R.transverseWidth j).toNNReal≤U j)
    (hlV:∀R,R∈V.cells→∀j,R.lower j<R.upper j→δ j≤(R.transverseWidth j).toNNReal)
    (huV:∀R,R∈V.cells→∀j,(R.transverseWidth j).toNNReal≤U j)
    (HT:∀R,R∈T.cells→R.lower i<R.upper i→ControlledContraction (cellLeftPoint m K i R) D J)
    (HV:∀R,R∈V.cells→R.lower i<R.upper i→ControlledContraction (cellLeftPoint m K i R) D J)
    (a:Fin d→ℤ) (hcell:∀R:RectangularCell d,R∈T.cells→R.translate a∈V.cells)
    (hstep:∀(n:ℕ)
      (F:QuantitativeEndpointSkeletonCarrierMaps T m K i n (atlasRankRates δ U D J i n))
      (G:QuantitativeEndpointSkeletonCarrierMaps V m K i n (atlasRankRates δ U D J i n)),
      SkeletonCarrierMaps.TranslationCovariant F.toSkeletonCarrierMaps G.toSkeletonCarrierMaps a hcell→
      ∀(R:RectangularCell d)(hR:R∈T.cells)(he:R.rank=n)(z:CellClosedDomain R),
        (actualQuantitativeExtension G HV (R.translate a) (hcell R hR)
          (by simpa only [RectangularCell.rank_translate] using he)).map (R.translateClosedPoint a z)=
          IntervalCarriers.realizationTranslation (a i) ((actualQuantitativeExtension F HT R hR he).map z))
    (n:ℕ) :
    SkeletonCarrierMaps.TranslationCovariant
      (actualQuantitativeSkeleton δ U D J hδ hlT huT HT n).toSkeletonCarrierMaps
      (actualQuantitativeSkeleton δ U D J hδ hlV huV HV n).toSkeletonCarrierMaps a hcell := by
  induction n with
  | zero => exact SkeletonCarrierMaps.empty_translationCovariant a hcell
  | succ n ih =>
    let F := actualQuantitativeSkeleton δ U D J hδ hlT huT HT n
    let G := actualQuantitativeSkeleton δ U D J hδ hlV huV HV n
    have hnext := EndpointSkeletonCarrierMaps.next_translationCovariant
      F.toEndpointSkeletonCarrierMaps G.toEndpointSkeletonCarrierMaps a hcell ih
      (actualQuantitativeExtension F HT) (actualQuantitativeExtension G HV) (hstep n F G ih)
    exact hnext

end
end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.CanonicalAtlasCovariance
section
/-! Translation covariance of the literal rank recursion driven by a
single normalized contraction family. -/

namespace AbelianTargets
noncomputable section
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d m K S : ℕ} {K₀ : Fin d→ℕ}
variable {T : IntegerRectangularTiling d K₀} {i : Fin d} {J : ℝ≥0}

theorem canonicalQuantitativeSkeleton_translate
    (H : IntervalCarriers.NormalizedContractionFamily m K S J) (hS : K₀ i≤S)
    (δ U : Fin d→ℝ≥0) (hδ : ∀j,0<δ j)
    (hl : ∀R,R∈T.cells→∀j,R.lower j<R.upper j→δ j≤(R.transverseWidth j).toNNReal)
    (hu : ∀R,R∈T.cells→∀j,(R.transverseWidth j).toNNReal≤U j)
    (a : Fin d→ℤ)
    (hl' : ∀R,R∈(T.translate a).cells→∀j,R.lower j<R.upper j→δ j≤(R.transverseWidth j).toNNReal)
    (hu' : ∀R,R∈(T.translate a).cells→∀j,(R.transverseWidth j).toNNReal≤U j)
    (n : ℕ) :
    SkeletonCarrierMaps.TranslationCovariant
      (actualQuantitativeSkeleton δ U (IntervalCarriers.uniformCarrierSpeed m K) J hδ hl hu
        (canonicalAtlasContractionProvider H T i hS) n).toSkeletonCarrierMaps
      (actualQuantitativeSkeleton δ U (IntervalCarriers.uniformCarrierSpeed m K) J hδ hl' hu'
        (canonicalAtlasContractionProvider H (T.translate a) i hS) n).toSkeletonCarrierMaps
      a (fun R hR=>T.cell_translate hR a) := by
  apply actualQuantitativeSkeleton_covariant δ U (IntervalCarriers.uniformCarrierSpeed m K) J
    hδ hl hu hl' hu' (canonicalAtlasContractionProvider H T i hS)
    (canonicalAtlasContractionProvider H (T.translate a) i hS) a
    (fun R hR=>T.cell_translate hR a)
  intro r F G hold R hR he z
  apply actualQuantitativeExtension_translate F a G
    (canonicalAtlasContractionProvider H T i hS)
    (canonicalAtlasContractionProvider H (T.translate a) i hS) hold
    (fun Q hQ hi p t=>?_) R hR he z
  exact canonicalCellContraction_translate H i Q hi _ a p t

end
end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.ComputedProjectedCovariance
section
/-! Covariance of a checked full-rank atlas gives covariance of its actual support projection. -/
namespace AbelianTargets
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SkeletonCarrierMaps
variable {d:ℕ} {K₀ K₁:Fin d→ℕ}
variable {T:IntegerRectangularTiling d K₀} {U:IntegerRectangularTiling d K₁}
variable {W:Type*} [Fintype W] {H:SimpleGraph W} (D:SupportTorsionData H)
variable {K:ℕ} {i:Fin d}

theorem TranslationCovariant.projectedMap_eq
    {F:SkeletonCarrierMaps T (2*D.power+1) K i (d+1)}
    {G:SkeletonCarrierMaps U (2*D.power+1) K i (d+1)}
    {a:Fin d→ℤ} {hcell:∀R:RectangularCell d,R∈T.cells→R.translate a∈U.cells}
    (hc:TranslationCovariant F G a hcell) (z:RealCoordinates d) :
    G.projectedMap D (translateCoordinates a z)=
      SupportPair.paritySwap H (a i) (F.projectedMap D z) := by
  exact F.projectedMap_translate_of_cell_maps D G a hcell
    (fun R hR z=>hc R hR R.rank_lt_succ_dimension z) z

end SkeletonCarrierMaps
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

/-- A tiling has only one data field; the remaining fields are proofs. -/
theorem IntegerRectangularTiling.eq_of_tiles_eq
    {d : ℕ} {K₀ : Fin d → ℕ}
    (T U : IntegerRectangularTiling d K₀) (h : T.tiles = U.tiles) :
    T = U := by
  cases T
  cases U
  cases h
  rfl

/-- Transport the existing canonical covariance theorem along a tiling
identity before projecting. The contraction family is the same on both sides. -/
theorem canonicalProjectedSkeleton_translate
    {d K S : ℕ} {K₀ : Fin d → ℕ}
    {T U : IntegerRectangularTiling d K₀}
    {W : Type*} [Fintype W] {G : SimpleGraph W}
    (D₀ : SupportTorsionData G) {i : Fin d} {J : ℝ≥0}
    (H : IntervalCarriers.NormalizedContractionFamily
      (2 * D₀.power + 1) K S J)
    (hS : K₀ i ≤ S) (δ V : Fin d → ℝ≥0) (hδ : ∀ j, 0 < δ j)
    (hlT : ∀ R, R ∈ T.cells → ∀ j, R.lower j < R.upper j →
      δ j ≤ (R.transverseWidth j).toNNReal)
    (huT : ∀ R, R ∈ T.cells → ∀ j,
      (R.transverseWidth j).toNNReal ≤ V j)
    (hlU : ∀ R, R ∈ U.cells → ∀ j, R.lower j < R.upper j →
      δ j ≤ (R.transverseWidth j).toNNReal)
    (huU : ∀ R, R ∈ U.cells → ∀ j,
      (R.transverseWidth j).toNNReal ≤ V j)
    (a : Lattice d) (hU : U = T.translate a) (z : RealCoordinates d) :
    (actualQuantitativeSkeleton δ V (IntervalCarriers.uniformCarrierSpeed
      (2 * D₀.power + 1) K) J hδ hlU huU
      (canonicalAtlasContractionProvider H U i hS) (d + 1)).toSkeletonCarrierMaps.projectedMap
        D₀ (translateCoordinates a z) =
      SupportPair.paritySwap G (a i)
        ((actualQuantitativeSkeleton δ V (IntervalCarriers.uniformCarrierSpeed
          (2 * D₀.power + 1) K) J hδ hlT huT
          (canonicalAtlasContractionProvider H T i hS) (d + 1)).toSkeletonCarrierMaps.projectedMap
            D₀ z) := by
  subst U
  exact SkeletonCarrierMaps.TranslationCovariant.projectedMap_eq D₀
    (canonicalQuantitativeSkeleton_translate H hS δ V hδ hlT huT a hlU huU
      (d + 1)) z

section Action
variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X]
variable [ContinuousVAdd (Lattice d) X]
variable {M₀ : AnisotropicClopenMarkers d L X} {S : ℕ}
variable {W : Type*} [Fintype W] {G : SimpleGraph W}

/-- Repointing by t subtracts t from the pointed atlas; translating back
by t recovers the original tiling, including its dependent proof fields. -/
theorem ContinuousMarkerBoxes.tiling_translate_repoint
    (B : ContinuousMarkerBoxes M₀ S) (hL : ∀ j, 1 ≤ L j) (hS : 6 ≤ S)
    (x : X) (t : Lattice d) :
    (B.tiling hL hS (t +ᵥ x)).translate t = B.tiling hL hS x := by
  apply IntegerRectangularTiling.eq_of_tiles_eq
  exact B.retainedTiles_repoint x t





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
variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X]
variable [ContinuousVAdd (Lattice d) X]
variable {M₀ : AnisotropicClopenMarkers d L X} {S : ℕ}
variable {W : Type*} [Fintype W] {G : SimpleGraph W}
open AbelianTargets.ContinuousMarkerBoxes

theorem solution
    (B : ContinuousMarkerBoxes M₀ S) (D₀ : SupportTorsionData G)
    (hL : ∀ j, 1 ≤ L j) (hS : 24 ≤ S) (K : ℕ) (i : Fin d) (J : ℝ≥0)
    (H : IntervalCarriers.NormalizedContractionFamily
      (2 * D₀.power + 1) K (6 * L i) J)
    (x : X) (t : Lattice d) (z : RealCoordinates d) :
    B.canonicalProjectedMap D₀ hL hS K i J H x (translateCoordinates t z) =
      SupportPair.paritySwap G (t i)
        (B.canonicalProjectedMap D₀ hL hS K i J H (t +ᵥ x) z) := by
  let δ : Fin d → ℝ≥0 := fun j => (L j : ℝ≥0) / (32 * ((2 * S + 1) ^ d : ℕ))
  let V : Fin d → ℝ≥0 := fun j => 6 * (L j : ℝ≥0)
  have hδ : ∀ j, 0 < δ j := by
    intro j
    have hj : 0 < L j := by have := hL j; omega
    dsimp [δ]
    positivity
  have hl (y : X) : ∀ R, R ∈ (B.tiling hL (by omega) y).cells →
      ∀ j, R.lower j < R.upper j → δ j ≤ (R.transverseWidth j).toNNReal := by
    intro R hR j hj
    exact (B.atlas_quantitative_widths hL hS y hR j).1 hj
  have hu (y : X) : ∀ R, R ∈ (B.tiling hL (by omega) y).cells →
      ∀ j, (R.transverseWidth j).toNNReal ≤ V j := by
    intro R hR j
    exact (B.atlas_quantitative_widths hL hS y hR j).2
  simpa only [canonicalProjectedMap, canonicalQuantitativeSkeleton, quantitativeSkeleton]
    using canonicalProjectedSkeleton_translate D₀ H (by rfl) δ V hδ
      (hl (t +ᵥ x)) (hu (t +ᵥ x)) (hl x) (hu x) t
      (B.tiling_translate_repoint hL (by omega) x t).symm z
