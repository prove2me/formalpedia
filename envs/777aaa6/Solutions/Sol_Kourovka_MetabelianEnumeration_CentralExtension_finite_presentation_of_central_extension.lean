-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CentralExtension.finite_presentation_of_central_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:10:29.077144+00:00
-- url     : https://prove2.me/submissions/7abc3c87-09e3-4724-b88c-cb9f72954ccf

import Definitions.Def_Kourovka_Presentations_CentralExtension
import Definitions.Def_Kourovka_Presentations_CentralExtensionPresentation
import Theorems.Thm_Kourovka_MetabelianEnumeration_CentralExtension_combined_correction
import Theorems.Thm_Kourovka_MetabelianEnumeration_CentralExtension_lift_inl_eq
import Theorems.Thm_Kourovka_MetabelianEnumeration_CentralExtension_lift_inr_eq


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CentralExtension
variable {α β : Type} [Fintype α] [Fintype β]
namespace Kourovka.MetabelianEnumeration.CentralExtension
theorem _root_.solution
    (R : List (FreeGroup α)) (S : List (FreeGroup β))
    {E : Type} [Group E]
    (π : E →* PresentedGroup (relSet R))
    (ι : PresentedGroup (relSet S) →* E)
    (hπ : Function.Surjective π) (hι : Function.Injective ι)
    (hexact : ι.range = π.ker) (hcentral : ι.range ≤ Subgroup.center E) :
    ∃ T : List (FreeGroup (α ⊕ β)), Nonempty (PresentedGroup (relSet T) ≃* E) := by
  classical
  choose t ht using fun a : α => hπ (PresentedGroup.of a)
  let z : β → E := fun b => ι (PresentedGroup.of b)
  have hz (b : β) : π (z b) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [← hexact]
    exact ⟨PresentedGroup.of b, rfl⟩
  have hπword (w : FreeGroup α) : π (FreeGroup.lift t w) =
      PresentedGroup.mk (relSet R) w := by
    have h : π.comp (FreeGroup.lift t) = PresentedGroup.mk (relSet R) := by
      apply FreeGroup.ext_hom
      intro a
      simpa only [MonoidHom.comp_apply, FreeGroup.lift_apply_of] using ht a
    exact DFunLike.congr_fun h w
  have hιword (w : FreeGroup β) : FreeGroup.lift z w =
      ι (PresentedGroup.mk (relSet S) w) := by
    have h : FreeGroup.lift z = ι.comp (PresentedGroup.mk (relSet S)) := by
      apply FreeGroup.ext_hom
      intro b
      simp [z, PresentedGroup.of]
    exact DFunLike.congr_fun h w
  have hc_exists (r : FreeGroup α) :
      ∃ w : FreeGroup β, r ∈ R → FreeGroup.lift t r = FreeGroup.lift z w := by
    by_cases hr : r ∈ R
    · have hmem : FreeGroup.lift t r ∈ ι.range := by
        rw [hexact]
        exact (MonoidHom.mem_ker).mpr (hπword r |>.trans (PresentedGroup.one_of_mem hr))
      obtain ⟨a, ha⟩ := hmem
      obtain ⟨w, hw⟩ := PresentedGroup.mk_surjective (relSet S) a
      exact ⟨w, fun _ => by rw [hιword, hw, ha]⟩
    · exact ⟨1, fun h => (hr h).elim⟩
  choose c hc using hc_exists
  let T := combinedRelations R S c
  let P := Combined R S c
  have hrels : ∀ r ∈ relSet T, FreeGroup.lift (Sum.elim t z) r = 1 := by
    intro r hr
    change r ∈ combinedRelations R S c at hr
    simp only [combinedRelations, List.mem_append, List.mem_map] at hr
    rcases hr with (⟨r, hr, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨⟨b, x⟩, _, rfl⟩
    · rw [map_mul, map_inv, lift_inl_eq, lift_inr_eq, hc r hr, mul_inv_cancel]
    · rw [lift_inr_eq, hιword, PresentedGroup.one_of_mem hs, map_one]
    · rw [map_commutatorElement, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
      apply commutatorElement_eq_one_iff_mul_comm.mpr
      exact (Subgroup.mem_center_iff.mp (hcentral ⟨PresentedGroup.of b, rfl⟩)
        (Sum.elim t z x)).symm
  let φ : P →* E := PresentedGroup.toGroup hrels
  let κ := kernelMap R S c
  let ψ := π.comp φ
  have hφinl (a : α) : φ (PresentedGroup.of (Sum.inl a)) = t a := by
    change FreeGroup.lift (Sum.elim t z) (FreeGroup.of (Sum.inl a)) = t a
    exact FreeGroup.lift_apply_of
  have hφinr (b : β) : φ (PresentedGroup.of (Sum.inr b)) = z b := by
    change FreeGroup.lift (Sum.elim t z) (FreeGroup.of (Sum.inr b)) = z b
    exact FreeGroup.lift_apply_of
  have hφκ : φ.comp κ = ι := by
    apply PresentedGroup.ext
    intro b
    change φ (kernelMap R S c (PresentedGroup.of b)) = ι (PresentedGroup.of b)
    rw [kernelMap_of, hφinr]
  have hψinl (a : α) : ψ (PresentedGroup.of (Sum.inl a)) = PresentedGroup.of a := by
    simp only [ψ, MonoidHom.comp_apply, hφinl, ht]
  have hψinr (b : β) : ψ (PresentedGroup.of (Sum.inr b)) = 1 := by
    simp only [ψ, MonoidHom.comp_apply, hφinr, hz]
  let q : P →* P ⧸ κ.range := QuotientGroup.mk' κ.range
  have hqκ (a : PresentedGroup (relSet S)) : q (κ a) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
  have hκword (w : FreeGroup β) :
      κ (PresentedGroup.mk (relSet S) w) =
        PresentedGroup.mk (relSet T) (FreeGroup.map Sum.inr w) := by
    change FreeGroup.lift (fun b => PresentedGroup.of (Sum.inr b)) w = _
    exact mk_inr_eq R S c w
  have hqinr (w : FreeGroup β) :
      q (PresentedGroup.mk (relSet T) (FreeGroup.map Sum.inr w)) = 1 := by
    rw [← hκword]
    exact hqκ _
  have hqinl (w : FreeGroup α) :
      FreeGroup.lift (fun a => q (PresentedGroup.of (Sum.inl a))) w =
        q (PresentedGroup.mk (relSet T) (FreeGroup.map Sum.inl w)) := by
    have h : FreeGroup.lift (fun a => q (PresentedGroup.of (Sum.inl a))) =
        (q.comp (PresentedGroup.mk (relSet T))).comp (FreeGroup.map Sum.inl) := by
      apply FreeGroup.ext_hom
      intro a
      simp [PresentedGroup.of]
      rfl
    exact DFunLike.congr_fun h w
  let sectionMap : PresentedGroup (relSet R) →* P ⧸ κ.range :=
    PresentedGroup.toGroup (f := fun a => q (PresentedGroup.of (Sum.inl a))) (by
      intro r hr
      rw [hqinl, combined_correction R S c r hr]
      exact hqinr _)
  have hsection : sectionMap.comp ψ = q := by
    apply PresentedGroup.ext
    intro x
    cases x with
    | inl a =>
      change sectionMap (ψ (PresentedGroup.of (Sum.inl a))) = _
      rw [hψinl]
      exact PresentedGroup.toGroup.of _
    | inr b =>
      change sectionMap (ψ (PresentedGroup.of (Sum.inr b))) = _
      rw [hψinr, map_one]
      have hb := hqκ (PresentedGroup.of b)
      change q (kernelMap R S c (PresentedGroup.of b)) = 1 at hb
      rw [kernelMap_of] at hb
      exact hb.symm
  have hker (p : P) (hp : ψ p = 1) : p ∈ κ.range := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q p = 1
    rw [← hsection, MonoidHom.comp_apply, hp, map_one]
  have hφinj : Function.Injective φ := by
    apply φ.ker_eq_bot_iff.mp
    apply le_antisymm _ bot_le
    intro p hp
    have hp' : φ p = 1 := hp
    have hψp : ψ p = 1 := by simp only [ψ, MonoidHom.comp_apply, hp', map_one]
    obtain ⟨a, rfl⟩ := hker p hψp
    have ha : a = 1 := hι (by
      have he := DFunLike.congr_fun hφκ a
      rw [MonoidHom.comp_apply] at he
      rw [← he, hp', map_one])
    simpa only [ha, map_one] using (Subgroup.one_mem (⊥ : Subgroup P))
  have hψsurj : Function.Surjective ψ := by
    intro g
    exact PresentedGroup.generated_by (relSet R) ψ.range
      (fun a => ⟨PresentedGroup.of (Sum.inl a), hψinl a⟩) g
  have hφsurj : Function.Surjective φ := by
    intro e
    obtain ⟨p, hp⟩ := hψsurj (π e)
    have hmem : e * (φ p)⁻¹ ∈ ι.range := by
      rw [hexact]
      change π (e * (φ p)⁻¹) = 1
      rw [map_mul, map_inv, ← hp]
      exact mul_inv_cancel _
    obtain ⟨a, ha⟩ := hmem
    refine ⟨κ a * p, ?_⟩
    rw [map_mul]
    have he := DFunLike.congr_fun hφκ a
    rw [MonoidHom.comp_apply] at he
    rw [he, ha, inv_mul_cancel_right]
  exact ⟨T, ⟨MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩⟩⟩
end Kourovka.MetabelianEnumeration.CentralExtension
