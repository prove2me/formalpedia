-- Prove2me | solution 1 for AbelianTargets.ContinuousMarkerBoxes.retainedTiles_eventually_eq
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T03:55:42.340002+00:00
-- url     : https://prove2.me/submissions/492bbd03-59e4-4a0b-bcd8-9ee199eba43e

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_ContinuousOrbitCuts
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_FixedOrbitPriorityCuts
import Definitions.Def_AT260939824_IntegerGridIntervals
import Definitions.Def_AT260939824_MarkerAtlasLocality
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerPriorities
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AT260939824_OrbitMarkerCuts
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_PriorityCuts
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RectangularAtlasBoundary
import Definitions.Def_AT260939824_RectangularBoundaryStrata
import Definitions.Def_AT260939824_RectangularCells
import Definitions.Def_AT260939824_RectangularLocalFiniteness
import Definitions.Def_AT260939824_RetainedMarkerTiles
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.MarkerAtlasLocality
section
/-! Finite local cut inputs determine actual retained tiles. In particular
the retained status of every fixed parent/cell is locally constant. -/

namespace AbelianTargets
noncomputable section
open Filter Topology
variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M : AnisotropicClopenMarkers d L X} {S : ℕ}

theorem ContinuousMarkerBoxes.Retained_iff_neighborhood (B : ContinuousMarkerBoxes M S)
    (x : X) (a : Lattice d) (R : RectangularCell d) :
    B.Retained x a R ↔ a +ᵥ x ∈ M.markers ∧ B.GridCell x a R ∧
      ∀ b ∈ inactiveOrbitNeighbors M 6 x a,
        (B.priority x b).val < (B.priority x a).val →
          Disjoint R.relativeInterior (B.markerBox x b).closedBox := by
  constructor
  · rintro ⟨ha,hgrid,hkeep⟩
    refine ⟨ha,hgrid,?_⟩
    intro b hb hp
    exact hkeep b ((mem_inactiveOrbitNeighbors_of_mem M 6 x a b ha).mp hb).1 hp
  · rintro ⟨ha,hgrid,hkeep⟩
    refine ⟨ha,hgrid,?_⟩
    intro b hb hp
    apply Set.disjoint_left.mpr
    intro z hzR hzb
    have hza := hgrid.subset_parent (R.relativeInterior_subset hzR)
    have hbn := B.parents_near_of_overlap x ha hb ⟨z,hza,hzb⟩
    exact Set.disjoint_left.mp (hkeep b hbn hp) hzR hzb

theorem ContinuousMarkerBoxes.Retained_eq_of_local_inputs
    (B : ContinuousMarkerBoxes M S) (x y : X) (a : Lattice d) (R : RectangularCell d)
    (hm : a +ᵥ x ∈ M.markers ↔ a +ᵥ y ∈ M.markers)
    (hN : inactiveOrbitNeighbors M 6 x a = inactiveOrbitNeighbors M 6 y a)
    (hp : ∀ b ∈ insert a (inactiveOrbitNeighbors M 6 x a),B.priority x b = B.priority y b)
    (hc : ∀ b ∈ insert a (inactiveOrbitNeighbors M 6 x a),∀ i,B.cuts x b i = B.cuts y b i) :
    B.Retained x a R ↔ B.Retained y a R := by
  have hca : ∀ i,B.cuts x a i = B.cuts y a i := fun i => hc a (by simp) i
  have hlevels : ∀ i,B.localCutLevels x a i = B.localCutLevels y a i := by
    intro i
    unfold localCutLevels
    rw [← hN]
    apply Finset.biUnion_congr rfl
    intro b hb
    rw [hc b (Finset.mem_insert_of_mem hb) i]
  have hgrid : B.GridCell x a R ↔ B.GridCell y a R := by
    unfold GridCell
    simp only [hlevels,hca]
  have hboxes : ∀ b ∈ inactiveOrbitNeighbors M 6 x a,B.markerBox x b = B.markerBox y b := by
    intro b hb
    apply RectangularCell.endpoint_pair_injective
    apply Prod.ext <;> funext i <;> dsimp [markerBox] <;>
      rw [hc b (Finset.mem_insert_of_mem hb) i]
  rw [B.Retained_iff_neighborhood,B.Retained_iff_neighborhood,← hm,← hgrid,← hN]
  apply and_congr_right
  intro ha
  apply and_congr_right
  intro hR
  apply forall_congr'
  intro b
  apply forall_congr'
  intro hb
  rw [← hp a (by simp),← hp b (Finset.mem_insert_of_mem hb),← hboxes b hb]

theorem ContinuousMarkerBoxes.retained_eventually_eq
    (B : ContinuousMarkerBoxes M S) (a : Lattice d) (R : RectangularCell d) (x : X) :
    ∀ᶠ y in 𝓝 x,B.Retained y a R ↔ B.Retained x a R := by
  letI : TopologicalSpace (Finset (Lattice d)) := ⊥
  letI : DiscreteTopology (Finset (Lattice d)) := ⟨rfl⟩
  have hn := (IsLocallyConstant.iff_continuous _).mpr
    (continuous_inactiveOrbitNeighbors M 6 a)
  have hm := (IsLocallyConstant.iff_continuous _).mpr
    ((continuous_markerFlag M.markers M.clopen).comp (continuous_const_vadd a))
  have hp : ∀ᶠ y in 𝓝 x,∀ b ∈ insert a (inactiveOrbitNeighbors M 6 x a),
      B.priority y b = B.priority x b := by
    apply (Filter.eventually_all_finset _).mpr
    intro b hb
    exact ((IsLocallyConstant.iff_continuous _).mpr (B.priority_continuous b)).eventually_eq x
  have hc : ∀ᶠ y in 𝓝 x,∀ b ∈ insert a (inactiveOrbitNeighbors M 6 x a),
      ∀ i,B.cuts y b i = B.cuts x b i := by
    apply (Filter.eventually_all_finset _).mpr
    intro b hb
    apply Filter.eventually_all.mpr
    intro i
    exact ((IsLocallyConstant.iff_continuous _).mpr (B.cuts_continuous b i)).eventually_eq x
  filter_upwards [hn.eventually_eq x,hm.eventually_eq x,hp,hc] with y hN hm hp hc
  have hmark : a +ᵥ x ∈ M.markers ↔ a +ᵥ y ∈ M.markers := by
    by_cases hx : a +ᵥ x ∈ M.markers <;> by_cases hy : a +ᵥ y ∈ M.markers <;>
      simp [markerFlag,hx,hy] at hm ⊢
  exact (B.Retained_eq_of_local_inputs x y a R hmark hN.symm
    (fun b hb => (hp b hb).symm) (fun b hb i => (hc b hb i).symm)).symm



theorem ContinuousMarkerBoxes.retained_parent_mem (B : ContinuousMarkerBoxes M S)
    {x : X} {a : Lattice d} {R : RectangularCell d} (hR : B.Retained x a R) :
    a ∈ rectangleParentCandidates L R := by
  simp only [rectangleParentCandidates,Fintype.mem_piFinset,Finset.mem_Icc]
  intro i
  have hr := (hR.2.1 i).2
  have hb := B.cuts_bounds x a i
  omega



end
end AbelianTargets

end

/-! Finite local cut inputs determine actual retained tiles. In particular
the retained status of every fixed parent/cell is locally constant. -/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
open Filter Topology
variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M : AnisotropicClopenMarkers d L X} {S : ℕ}
open AbelianTargets.ContinuousMarkerBoxes

theorem solution
    (B : ContinuousMarkerBoxes M S) (R : RectangularCell d) (x : X) :
    ∀ᶠ y in 𝓝 x,R ∈ B.retainedTiles y ↔ R ∈ B.retainedTiles x := by
  have h : ∀ᶠ y in 𝓝 x,∀ a ∈ rectangleParentCandidates L R,
      B.Retained y a R ↔ B.Retained x a R := by
    apply (Filter.eventually_all_finset _).mpr
    intro a ha
    exact B.retained_eventually_eq a R x
  filter_upwards [h] with y hy
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,(hy a (B.retained_parent_mem ha)).mp ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨a,(hy a (B.retained_parent_mem ha)).mpr ha⟩
