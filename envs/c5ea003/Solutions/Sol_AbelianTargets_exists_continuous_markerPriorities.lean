-- Prove2me | solution 1 for AbelianTargets.exists_continuous_markerPriorities
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:13:00.830217+00:00
-- url     : https://prove2.me/submissions/f28894da-ca2b-4d2c-b51e-e55c38ee843c

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerPriorities
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Profinite
import Theorems.Thm_AbelianTargets_exists_continuous_finite_coloring
import Theorems.Thm_AbelianTargets_exists_countable_anisotropic_independent_cover
import Theorems.Thm_AbelianTargets_neighbor_clopen_anisotropicDisplacementGraph

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.MarkerPriorities
section
/-!
# Continuous marker priorities with a scale-independent color bound

The marker proximity graph is the actual induced finite-displacement
graph. Its finite neighbors are counted by the anisotropic packing bound.
The general continuous finite-coloring theorem supplies the priorities.
-/

namespace AbelianTargets

noncomputable section

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X]





theorem zero_mem_scaledMarkerNeighborhood (M : AnisotropicClopenMarkers d L X)
    (S : ℕ) (x : M.markers) : 0 ∈ scaledMarkerNeighborhood M S x := by
  apply (mem_scaledMarkerNeighborhood M S x 0).mpr
  refine ⟨?_,by simpa using x.property⟩
  intro i
  change -(S : ℤ)*(L i : ℤ) ≤ 0 ∧ 0 ≤ (S : ℤ)*(L i : ℤ)
  have hpos : 0 ≤ (S : ℤ)*(L i : ℤ) := by positivity
  exact ⟨by simpa only [neg_mul] using neg_nonpos.mpr hpos,hpos⟩





theorem markerNeighborList_card_le (M : AnisotropicClopenMarkers d L X)
    (hL : ∀ i,1 ≤ L i) (S : ℕ) (x : M.markers) :
    (markerNeighborList M S x).card ≤ (2*S+1)^d-1 := by
  classical
  unfold markerNeighborList
  calc
    _ ≤ (((scaledMarkerNeighborhood M S x).erase 0).attach).card := Finset.card_image_le
    _ = (scaledMarkerNeighborhood M S x).card-1 := by
      rw [Finset.card_attach,Finset.card_erase_of_mem (zero_mem_scaledMarkerNeighborhood M S x)]
    _ ≤ (2*S+1)^d-1 := Nat.sub_le_sub_right (scaledMarkerNeighborhood_card_le M hL S x) 1



theorem markerProximity_adj_neighbor (M : AnisotropicClopenMarkers d L X) (S : ℕ)
    (free : IsFree (G := Lattice d) (X := X)) (x y : M.markers)
    (hxy : (markerProximityGraph M S free).Adj y x) : y ∈ markerNeighborList M S x := by
  classical
  obtain ⟨g,hg,hgy⟩ := (markerProximityGraph M S free).symm hxy
  obtain ⟨hbound,hne⟩ := (mem_anisotropicDisplacements (fun i => S*L i) g).mp hg
  have hgN : g ∈ (scaledMarkerNeighborhood M S x).erase 0 := by
    apply Finset.mem_erase.mpr
    refine ⟨hne,(mem_scaledMarkerNeighborhood M S x g).mpr ⟨?_,hgy ▸ y.property⟩⟩
    intro i
    have hi := hbound i
    rw [abs_le] at hi
    simpa only [Nat.cast_mul,neg_mul] using hi
  apply Finset.mem_image.mpr
  refine ⟨⟨g,hgN⟩,Finset.mem_attach _ _,?_⟩
  exact Subtype.ext hgy

variable [ContinuousVAdd (Lattice d) X] [T1Space X] [SecondCountableTopology X]

omit [T1Space X] [SecondCountableTopology X] in
theorem neighbor_clopen_markerProximityGraph (M : AnisotropicClopenMarkers d L X)
    (S : ℕ) (free : IsFree (G := Lattice d) (X := X))
    (U : Set M.markers) (hU : IsClopen U) :
    IsClopen (NeighborSet (markerProximityGraph M S free) U) := by
  have hImage : IsClopen (Subtype.val '' U : Set X) :=
    ⟨M.clopen.isClosed.isClosedEmbedding_subtypeVal.isClosedMap _ hU.isClosed,
      M.clopen.isOpen.isOpenMap_subtype_val _ hU.isOpen⟩
  have heq : NeighborSet (markerProximityGraph M S free) U =
      Subtype.val ⁻¹' NeighborSet (anisotropicDisplacementGraph (fun i => S*L i) free)
        (Subtype.val '' U) := by
    ext y
    constructor
    · rintro ⟨x,hx,hxy⟩
      exact ⟨x.val,⟨x,hx,rfl⟩,hxy⟩
    · rintro ⟨x,⟨x',hx',rfl⟩,hxy⟩
      exact ⟨x',hx',hxy⟩
  rw [heq]
  exact (neighbor_clopen_anisotropicDisplacementGraph _ free _ hImage).preimage continuous_subtype_val



end

end AbelianTargets

end

/-!
# Continuous marker priorities with a scale-independent color bound

The marker proximity graph is the actual induced finite-displacement
graph. Its finite neighbors are counted by the anisotropic packing bound.
The general continuous finite-coloring theorem supplies the priorities.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X]
variable [ContinuousVAdd (Lattice d) X] [T1Space X] [SecondCountableTopology X]

theorem solution (M : AnisotropicClopenMarkers d L X)
    (hL : ∀ i,1 ≤ L i) (S : ℕ) (zeroDim : ZeroDimensional X)
    (free : IsFree (G := Lattice d) (X := X)) :
    ∃ c : M.markers → Fin ((2*S+1)^d),Continuous c ∧
      ∀ x y,(markerProximityGraph M S free).Adj x y → c x ≠ c y := by
  classical
  obtain ⟨C,hclopen,hindep,hcover⟩ := exists_countable_anisotropic_independent_cover
    (fun i => S*L i) zeroDim free
  let C' := fun n => (Subtype.val : M.markers → X) ⁻¹' C n
  have hC' : ∀ n,IsClopen (C' n) := fun n => (hclopen n).preimage continuous_subtype_val
  have hi' : ∀ n,GraphIndependent (markerProximityGraph M S free) (C' n) := by
    intro n x hx y hy hxy
    exact hindep n x.val hx y.val hy hxy
  have hc' : ∀ x : M.markers,∃ n,x ∈ C' n := fun x => hcover x.val
  have hP : 1 ≤ (2*S+1)^d := Nat.one_le_pow _ _ (by omega)
  obtain ⟨c,hc,hproper⟩ := exists_continuous_finite_coloring (markerProximityGraph M S free) C'
    hC' hi' hc' (neighbor_clopen_markerProximityGraph M S free)
    ((2*S+1)^d-1) (markerNeighborList M S)
    (markerNeighborList_card_le M hL S) (markerProximity_adj_neighbor M S free)
  have heq : (2*S+1)^d-1+1 = (2*S+1)^d := by omega
  exact ⟨fun x => Fin.cast heq (c x),
    (continuous_of_discreteTopology (f := fun j => Fin.cast heq j)).comp hc,
    fun x y hxy he => hproper x y hxy (Fin.cast_injective heq he)⟩
