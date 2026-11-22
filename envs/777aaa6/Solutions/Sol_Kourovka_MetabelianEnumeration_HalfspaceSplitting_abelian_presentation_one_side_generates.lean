-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceSplitting.abelian_presentation_one_side_generates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:14:56.93818+00:00
-- url     : https://prove2.me/submissions/932ed72d-396c-47e8-bf0e-3de4d7feb310

import Definitions.Def_Kourovka_Modules_ModuleRealization
import Mathlib.GroupTheory.HNNExtension
import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceSplitting_left_eq_right
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceSplitting_abelian_twist_collapse

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceSplitting
variable {N : Type*} [Group N]
namespace Kourovka.MetabelianEnumeration.HalfspaceSplitting
theorem _root_.solution {X : Type*}
    (R : Set (FreeGroup X)) (S T : Set X)
    (hcover : ∀ x, x ∈ S ∨ x ∈ T)
    (hrel : ∀ r ∈ R,
      r ∈ Subgroup.closure (FreeGroup.of '' S) ∨
      r ∈ Subgroup.closure (FreeGroup.of '' T))
    (habelian : ∀ a b : PresentedGroup R, Commute a b) :
    Subgroup.closure (PresentedGroup.of '' S : Set (PresentedGroup R)) = ⊤ ∨
    Subgroup.closure (PresentedGroup.of '' T : Set (PresentedGroup R)) = ⊤ := by
  classical
  let A : Subgroup (PresentedGroup R) := Subgroup.closure (PresentedGroup.of '' S)
  let B : Subgroup (PresentedGroup R) := Subgroup.closure (PresentedGroup.of '' T)
  let C := A ⊓ B
  let g : X → Twist C := fun x =>
    if x ∈ S then left C (PresentedGroup.of x) else right C (PresentedGroup.of x)
  have hgS : ∀ x ∈ S, g x = left C (PresentedGroup.of x) := by
    intro x hx; simp [g, hx]
  have hgT : ∀ x ∈ T, g x = right C (PresentedGroup.of x) := by
    intro x hx
    by_cases hs : x ∈ S
    · rw [hgS x hs]
      exact left_eq_right C ⟨Subgroup.subset_closure ⟨x, hs, rfl⟩,
        Subgroup.subset_closure ⟨x, hx, rfl⟩⟩
    · simp [g, hs]
  have hS : Set.EqOn (FreeGroup.lift g)
      ((left C).comp (PresentedGroup.mk R))
      (Subgroup.closure (FreeGroup.of '' S)) := by
    apply MonoidHom.eqOn_closure
    rintro _ ⟨x, hx, rfl⟩
    simpa only [FreeGroup.lift_apply_of, MonoidHom.comp_apply, PresentedGroup.of] using hgS x hx
  have hT : Set.EqOn (FreeGroup.lift g)
      ((right C).comp (PresentedGroup.mk R))
      (Subgroup.closure (FreeGroup.of '' T)) := by
    apply MonoidHom.eqOn_closure
    rintro _ ⟨x, hx, rfl⟩
    simpa only [FreeGroup.lift_apply_of, MonoidHom.comp_apply, PresentedGroup.of] using hgT x hx
  have hkill : ∀ r ∈ R, FreeGroup.lift g r = 1 := by
    intro r hr
    rcases hrel r hr with h | h
    · rw [hS h]
      simp only [MonoidHom.comp_apply, PresentedGroup.one_of_mem hr, map_one]
    · rw [hT h]
      simp only [MonoidHom.comp_apply, PresentedGroup.one_of_mem hr, map_one]
  let f : PresentedGroup R →* Twist C := PresentedGroup.toGroup hkill
  have hfS : Set.EqOn f (left C) A := by
    apply MonoidHom.eqOn_closure
    rintro _ ⟨x, hx, rfl⟩
    simpa only [f, PresentedGroup.toGroup.of] using hgS x hx
  have hfT : Set.EqOn f (right C) B := by
    apply MonoidHom.eqOn_closure
    rintro _ ⟨x, hx, rfl⟩
    simpa only [f, PresentedGroup.toGroup.of] using hgT x hx
  have hsup : A ⊔ B = ⊤ := by
    apply top_unique
    rw [← PresentedGroup.closure_range_of]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨x, rfl⟩
    rcases hcover x with hx | hx
    · exact (le_sup_left : A ≤ A ⊔ B) (Subgroup.subset_closure ⟨x, hx, rfl⟩ : PresentedGroup.of x ∈ A)
    · exact (le_sup_right : B ≤ A ⊔ B) (Subgroup.subset_closure ⟨x, hx, rfl⟩ : PresentedGroup.of x ∈ B)
  rcases abelian_twist_collapse C A B habelian f (fun _ h => hfS h)
      (fun _ h => hfT h) with h | h
  · right
    have hab : A ≤ B := h.trans inf_le_right
    simpa only [sup_eq_right.mpr hab] using hsup
  · left
    have hba : B ≤ A := h.trans inf_le_left
    simpa only [sup_eq_left.mpr hba] using hsup
end Kourovka.MetabelianEnumeration.HalfspaceSplitting
