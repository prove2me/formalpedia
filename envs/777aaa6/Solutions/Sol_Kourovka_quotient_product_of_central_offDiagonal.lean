-- Prove2me | solution 1 for Kourovka.quotient_product_of_central_offDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:36:56.496593+00:00
-- url     : https://prove2.me/submissions/6dbfd85e-2f5e-499f-af8e-58e47a321841

import Definitions.Def_Kourovka_EventualCentrality
import Definitions.Def_Kourovka_QuotientProducts
import Theorems.Thm_Kourovka_CenterQuotients_productEquiv_mk
import Theorems.Thm_Kourovka_CenterQuotients_quotientMap_surjective
import Theorems.Thm_Kourovka_ProductPaths_axis_axis_same
import Theorems.Thm_Kourovka_ProductPaths_axis_false
import Theorems.Thm_Kourovka_ProductPaths_axis_true
import Theorems.Thm_Kourovka_ProductPaths_iterateHom_apply
import Theorems.Thm_Kourovka_ProductPaths_path_cons
import Theorems.Thm_Kourovka_ProductPaths_path_nil
attribute [local simp] Kourovka.CenterQuotients.productEquiv_mk
attribute [local simp] Kourovka.ProductPaths.axis_axis_same
attribute [local simp] Kourovka.ProductPaths.axis_false
attribute [local simp] Kourovka.ProductPaths.axis_true
attribute [local simp] Kourovka.ProductPaths.iterateHom_apply
attribute [local simp] Kourovka.ProductPaths.path_cons
attribute [local simp] Kourovka.ProductPaths.path_nil



set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka
theorem _root_.solution (f : A × B →* A × B)
    (hf : Function.Surjective f)
    (h12 : ∀ b : B, (f (1, b)).1 ∈ Subgroup.center A)
    (h21 : ∀ a : A, (f (a, 1)).2 ∈ Subgroup.center B) :
    ∃ (u : A ⧸ Subgroup.center A →* A ⧸ Subgroup.center A)
      (v : B ⧸ Subgroup.center B →* B ⧸ Subgroup.center B),
      Function.Surjective u ∧ Function.Surjective v ∧
      ∀ x y, CenterQuotients.quotientMap f hf (CenterQuotients.productEquiv (x, y)) =
        CenterQuotients.productEquiv (u x, v y) := by
  let E := CenterQuotients.productEquiv (A := A) (B := B)
  let H := E.symm.toMonoidHom.comp ((CenterQuotients.quotientMap f hf).comp E.toMonoidHom)
  have hH : Function.Surjective H :=
    E.symm.surjective.comp ((CenterQuotients.quotientMap_surjective f hf).comp E.surjective)
  have hrep (a : A) (b : B) :
      H (QuotientGroup.mk a, QuotientGroup.mk b) =
        (QuotientGroup.mk (f (a, b)).1, QuotientGroup.mk (f (a, b)).2) := by
    apply E.injective
    change E (E.symm (CenterQuotients.quotientMap f hf
      (E (QuotientGroup.mk a, QuotientGroup.mk b)))) = _
    rw [E.apply_symm_apply]
    change CenterQuotients.quotientMap f hf
      (CenterQuotients.productEquiv (QuotientGroup.mk a, QuotientGroup.mk b)) =
      CenterQuotients.productEquiv (QuotientGroup.mk (f (a, b)).1, QuotientGroup.mk (f (a, b)).2)
    rw [CenterQuotients.productEquiv_mk, CenterQuotients.productEquiv_mk]
    rfl
  let u := (MonoidHom.fst (A ⧸ Subgroup.center A) (B ⧸ Subgroup.center B)).comp
    (H.comp (MonoidHom.inl (A ⧸ Subgroup.center A) (B ⧸ Subgroup.center B)))
  let v := (MonoidHom.snd (A ⧸ Subgroup.center A) (B ⧸ Subgroup.center B)).comp
    (H.comp (MonoidHom.inr (A ⧸ Subgroup.center A) (B ⧸ Subgroup.center B)))
  have hleft (x : A ⧸ Subgroup.center A) : H (x, 1) = (u x, 1) := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    apply Prod.ext
    · rfl
    · have he := congrArg Prod.snd (hrep a 1)
      simpa only [QuotientGroup.mk_one, (QuotientGroup.eq_one_iff _).mpr (h21 a)] using he
  have hright (y : B ⧸ Subgroup.center B) : H (1, y) = (1, v y) := by
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    apply Prod.ext
    · have he := congrArg Prod.fst (hrep 1 b)
      simpa only [QuotientGroup.mk_one, (QuotientGroup.eq_one_iff _).mpr (h12 b)] using he
    · rfl
  have hprod (x : A ⧸ Subgroup.center A) (y : B ⧸ Subgroup.center B) :
      H (x, y) = (u x, v y) := by
    calc
      H (x, y) = H ((x, 1) * (1, y)) := by simp
      _ = H (x, 1) * H (1, y) := H.map_mul _ _
      _ = (u x, v y) := by rw [hleft, hright]; simp
  refine ⟨u, v, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨⟨a, b⟩, he⟩ := hH (x, 1)
    exact ⟨a, congrArg Prod.fst ((hprod a b).symm.trans he)⟩
  · intro y
    obtain ⟨⟨a, b⟩, he⟩ := hH (1, y)
    exact ⟨b, congrArg Prod.snd ((hprod a b).symm.trans he)⟩
  · intro x y
    have he := congrArg E (hprod x y)
    change E (E.symm (CenterQuotients.quotientMap f hf (E (x, y)))) = E (u x, v y) at he
    simpa only [E.apply_symm_apply] using he
end Kourovka
