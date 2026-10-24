-- Prove2me | solution 1 for NoUniversalFSigma.lemma2_4
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-23T06:52:43.629977+00:00
-- url     : https://prove2.me/submissions/77ddb566-d513-49f9-956d-37ced7468f93

import Definitions.Def_NoUniversalFSigma261031052
import Mathlib.Topology.Baire.Lemmas

/-!
# Category preliminaries

This file proves the continuous-restriction lemma and the elementary category
facts used in Section 2.3 of arXiv:2610.31052.
-/

open Set Filter Topology TopologicalSpace

namespace NoUniversalFSigma

universe u v

/-- Lemma 2.4: a Baire-measurable map with second-countable target is
continuous on a comeager `Gδ` subspace of a Polish space. -/
theorem baire_measurable_continuous_on_comeagre_gdelta {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X]
    [TopologicalSpace Y] [SecondCountableTopology Y]
    (f : X → Y) (hf : IsBaireMeasurable f) :
    ∃ C : Set X, IsGδ C ∧ IsMeagre Cᶜ ∧ Continuous (fun x : C => f x) := by
  classical
  have happrox (U : countableBasis Y) :
      ∃ V : Set X, IsOpen V ∧ (f ⁻¹' (U : Set Y)) =ᵇ V :=
    (hf U (isOpen_of_mem_countableBasis U.property)).residualEq_isOpen
  choose V hV hEq using happrox
  have hsim : ∀ᶠ x in residual X,
      ∀ U : countableBasis Y, f x ∈ (U : Set Y) ↔ x ∈ V U := by
    apply eventually_countable_forall.mpr
    intro U
    exact eventuallyEq_set.mp (hEq U)
  obtain ⟨C, hC, hCd, hCp⟩ := eventually_residual.mp hsim
  refine ⟨C, hC, ?_, ?_⟩
  · simpa only [IsMeagre, compl_compl] using residual_of_dense_Gδ hC hCd
  · apply (isBasis_countableBasis Y).continuous_iff.mpr
    intro U hU
    have hpre : (fun x : C => f x) ⁻¹' U =
        (Subtype.val : C → X) ⁻¹' V ⟨U, hU⟩ := by
      ext x
      exact hCp x x.property ⟨U, hU⟩
    rw [hpre]
    exact (hV ⟨U, hU⟩).preimage continuous_subtype_val

/-- Lemma 2.5(1). -/
theorem baireSpace_of_dense_gdelta {X : Type u} [TopologicalSpace X]
    [BaireSpace X] {C : Set X} (hC : IsGδ C) (hd : Dense C) : BaireSpace C :=
  hC.baireSpace_of_dense hd

/-- Lemma 2.5(2), in the dense-open form. -/
theorem dense_open_preimage {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {p : X → Y}
    (hp : Continuous p) (hpo : IsOpenMap p) {U : Set Y}
    (hU : IsOpen U) (hd : Dense U) :
    IsOpen (p ⁻¹' U) ∧ Dense (p ⁻¹' U) :=
  ⟨hU.preimage hp, hd.preimage hpo⟩

/-- A continuous open map pulls comeager `Gδ` sets back to comeager `Gδ` sets. -/
theorem comeager_gdelta_preimage {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {p : X → Y}
    (hp : Continuous p) (hpo : IsOpenMap p) {C : Set Y}
    (hC : IsGδ C) (hm : IsMeagre Cᶜ) :
    IsGδ (p ⁻¹' C) ∧ IsMeagre (p ⁻¹' C)ᶜ := by
  refine ⟨isGδ_induced hp hC, ?_⟩
  exact hm.preimage_of_isOpenMap hp hpo

/-- Countable intersections of comeager sets are comeager. -/
theorem comeager_iInter {X : Type u} [TopologicalSpace X]
    {ι : Sort v} [Countable ι] {C : ι → Set X}
    (hm : ∀ i, IsMeagre (C i)ᶜ) : IsMeagre (⋂ i, C i)ᶜ := by
  simp only [IsMeagre, compl_compl] at hm ⊢
  exact countable_iInter_mem.mpr hm

/-- Countable intersections preserve both the comeager and `Gδ` properties. -/
theorem comeager_gdelta_iInter {X : Type u} [TopologicalSpace X]
    {ι : Sort v} [Countable ι] {C : ι → Set X}
    (hC : ∀ i, IsGδ (C i)) (hm : ∀ i, IsMeagre (C i)ᶜ) :
    IsGδ (⋂ i, C i) ∧ IsMeagre (⋂ i, C i)ᶜ :=
  ⟨IsGδ.iInter hC, comeager_iInter hm⟩

/-- A comeager set meets every nonempty open set in a Baire space. -/
theorem comeager_inter_open_nonempty {X : Type u} [TopologicalSpace X]
    [BaireSpace X] {C U : Set X} (hm : IsMeagre Cᶜ)
    (hU : IsOpen U) (hne : U.Nonempty) : (C ∩ U).Nonempty := by
  have hr : C ∈ residual X := by simpa only [IsMeagre, compl_compl] using hm
  simpa only [inter_comm] using (dense_of_mem_residual hr).inter_open_nonempty U hU hne

/-- Homeomorphisms preserve comeager sets. -/
theorem comeager_image_homeomorph {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) {C : Set X} (hm : IsMeagre Cᶜ) : IsMeagre (h '' C)ᶜ := by
  rw [h.image_eq_preimage_symm]
  exact hm.preimage_of_isOpenMap h.symm.continuous h.symm.isOpenMap

/-- In particular, translations in a topological additive group preserve
comeager sets, as in Lemma 2.5(3). -/
theorem comeager_image_add_right {X : Type u} [TopologicalSpace X]
    [AddGroup X] [IsTopologicalAddGroup X] (a : X) {C : Set X}
    (hm : IsMeagre Cᶜ) : IsMeagre ((fun x : X => x + a) '' C)ᶜ :=
  comeager_image_homeomorph (Homeomorph.addRight a) hm

/-- A countable list of translation requirements can be met simultaneously
inside any nonempty open set. This supplies the fixed first endpoint in the
comparison-of-derivatives argument. -/
theorem exists_mem_open_with_countably_many_translates
    {X : Type u} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X]
    [BaireSpace X] {C U : Set X} (hm : IsMeagre Cᶜ)
    (hU : IsOpen U) (hne : U.Nonempty) (a : ℕ → X) :
    ∃ v ∈ U, ∀ n, v - a n ∈ C := by
  have hr : C ∈ residual X := by simpa only [IsMeagre, compl_compl] using hm
  have htrans (n : ℕ) : ∀ᶠ v in residual X, v - a n ∈ C := by
    have ho : IsOpenMap (fun v : X => v - a n) := by
      simpa only [sub_eq_add_neg] using (Homeomorph.addRight (-a n)).isOpenMap
    exact tendsto_residual_of_isOpenMap (continuous_id.sub continuous_const) ho hr
  have hforall : ∀ᶠ v in residual X, ∀ n, v - a n ∈ C :=
    eventually_countable_forall.mpr htrans
  obtain ⟨v, hvU, hv⟩ :=
    (dense_of_mem_residual hforall).inter_open_nonempty U hU hne
  exact ⟨v, hvU, hv⟩

/-- A countable relatively closed cover of a dense `Gδ` subset of a
nonempty product is uniform on the trace of some nonempty open rectangle.
This is the category step in the rectangle lemma of Section 4. -/
theorem exists_open_rectangle_of_closed_cover
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] [Nonempty Y] [BaireSpace (X × Y)]
    {D : Set (X × Y)} (hD : IsGδ D) (hd : Dense D)
    (A : ℕ → Set D) (hA : ∀ n, IsClosed (A n))
    (hcover : ⋃ n, A n = univ) :
    ∃ (n : ℕ) (U : Set X) (V : Set Y),
      IsOpen U ∧ IsOpen V ∧ U.Nonempty ∧ V.Nonempty ∧
        ∀ z : D, (z : X × Y) ∈ U ×ˢ V → z ∈ A n := by
  letI : BaireSpace D := hD.baireSpace_of_dense hd
  letI : Nonempty D := hd.nonempty.to_subtype
  obtain ⟨n, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hA hcover
  obtain ⟨W, hWo, hWeq⟩ :=
    isOpen_induced_iff.mp (isOpen_interior (s := A n))
  have hxW : (x : X × Y) ∈ W := by
    change x ∈ (Subtype.val : D → X × Y) ⁻¹' W
    rw [hWeq]
    exact hx
  obtain ⟨U, V, hU, hV, hxU, hxV, hUV⟩ :=
    isOpen_prod_iff.mp hWo x.val.1 x.val.2 hxW
  refine ⟨n, U, V, hU, hV, ⟨_, hxU⟩, ⟨_, hxV⟩, ?_⟩
  intro z hz
  apply interior_subset
  rw [← hWeq]
  exact hUV hz

/-- A closed condition on a relatively continuous map extends from a dense
set to all points of its domain lying in a prescribed ambient open set.
The larger domain need not itself be open or closed. -/
theorem closed_condition_of_dense_on_open
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {S D W : Set X} (hDS : D ⊆ S) (hd : Dense D) (hW : IsOpen W)
    {g : S → Y} (hg : Continuous g) {F : Set Y} (hF : IsClosed F)
    (hprop : ∀ z : S, (z : X) ∈ D ∩ W → g z ∈ F) :
    ∀ z : S, (z : X) ∈ W → g z ∈ F := by
  have hSD : Dense ((Subtype.val : S → X) ⁻¹' D) := by
    apply Subtype.dense_iff.mpr
    have hi : (Subtype.val : S → X) '' ((Subtype.val : S → X) ⁻¹' D) = D := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hx
        exact ⟨⟨x, hDS hx⟩, hx, rfl⟩
    rw [hi, hd.closure_eq]
    exact subset_univ S
  have hsub : ((Subtype.val : S → X) ⁻¹' W) ∩
      ((Subtype.val : S → X) ⁻¹' D) ⊆ g ⁻¹' F := by
    intro z hz
    exact hprop z ⟨hz.2, hz.1⟩
  intro z hz
  exact closure_minimal hsub (hF.preimage hg)
    (hSD.open_subset_closure_inter (hW.preimage continuous_subtype_val) hz)

end NoUniversalFSigma


universe u v

theorem solution {X : Type u} {Y : Type v} [TopologicalSpace X] [PolishSpace X] [TopologicalSpace Y] [SecondCountableTopology Y] (f : X → Y) (hf : NoUniversalFSigma.IsBaireMeasurable f) : ∃ C : Set X, IsGδ C ∧ IsMeagre Cᶜ ∧ Continuous (fun x : C => f x) :=
  NoUniversalFSigma.baire_measurable_continuous_on_comeagre_gdelta f hf
