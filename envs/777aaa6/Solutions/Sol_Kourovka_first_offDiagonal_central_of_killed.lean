-- Prove2me | solution 1 for Kourovka.first_offDiagonal_central_of_killed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:41:45.74421+00:00
-- url     : https://prove2.me/submissions/a7af1095-36e6-4d19-b9aa-b6eaa70357f7

import Definitions.Def_Kourovka_MixedPaths
import Definitions.Def_Kourovka_CenterQuotients
import Definitions.Def_Kourovka_EventualCentrality
import Theorems.Thm_Kourovka_CenterQuotients_productEquiv_mk
import Theorems.Thm_Kourovka_CenterQuotients_quotientMap_surjective
import Theorems.Thm_Kourovka_CenterQuotients_retract_trivial_of_killed
import Theorems.Thm_Kourovka_ProductHom_commute
import Theorems.Thm_Kourovka_ProductHom_right_center
import Theorems.Thm_Kourovka_ProductHom_row_surjective
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
theorem _root_.solution [Group.FG A] [Group.FG B] [IsSolvable A]
    (f : A × B →* A × B) (hf : Function.Surjective f)
    (hk : ∀ b : B, f ((f (1, b)).1, 1) ∈ Subgroup.center (A × B)) :
    ∀ b : B, (f (1, b)).1 ∈ Subgroup.center A := by
  let row : A × B →* A := (MonoidHom.fst A B).comp f
  let P := (ProductHom.left row).range
  let Q := (ProductHom.right row).range
  have hrow : Function.Surjective row := Prod.fst_surjective.comp hf
  have hc : ∀ p : P, ∀ q : Q, Commute (p : A) (q : A) := by
    rintro ⟨p, a, rfl⟩ ⟨q, b, rfl⟩
    exact ProductHom.commute row a b
  have hcover : ∀ a : A, ∃ p : P, ∃ q : Q, (p : A) * q = a := by
    intro a
    obtain ⟨x, y, hxy⟩ := ProductHom.row_surjective row hrow a
    exact ⟨(ProductHom.left row).rangeRestrict x, (ProductHom.right row).rangeRestrict y, hxy⟩
  let E := CentralProducts.quotientEquiv P Q hc hcover
  let U := P ⧸ Subgroup.center P
  let T := Q ⧸ Subgroup.center Q
  let V := B ⧸ Subgroup.center B
  let D : (U × T) × V ≃* (A × B) ⧸ Subgroup.center (A × B) :=
    (E.prodCongr (MulEquiv.refl V)).trans CenterQuotients.productEquiv
  let i : T →* (A × B) ⧸ Subgroup.center (A × B) :=
    D.toMonoidHom.comp ((MonoidHom.inl (U × T) V).comp (MonoidHom.inr U T))
  let r : (A × B) ⧸ Subgroup.center (A × B) →* T :=
    (MonoidHom.snd U T).comp ((MonoidHom.fst (U × T) V).comp D.symm.toMonoidHom)
  have hri : ∀ t, r (i t) = t := by
    intro t
    change (D.symm (D ((1, t), 1))).1.2 = t
    rw [D.symm_apply_apply]
  have hi (q : Q) : i (QuotientGroup.mk q) = QuotientGroup.mk ((q : A), (1 : B)) := by
    change CenterQuotients.productEquiv (A := A) (B := B) (E (1, QuotientGroup.mk q), 1) = _
    have he : E (1, QuotientGroup.mk q) = QuotientGroup.mk (q : A) := by
      change CentralProducts.quotientMultiply P Q hc hcover (1, QuotientGroup.mk q) = _
      change CentralProducts.leftQuotient P Q hc hcover 1 *
        CentralProducts.rightQuotient P Q hc hcover (QuotientGroup.mk q) = _
      rw [map_one, one_mul]
      rfl
    rw [he]
    simpa only [map_one] using CenterQuotients.productEquiv_mk (q : A) (1 : B)
  have hkill : ∀ t, CenterQuotients.quotientMap f hf (i t) = 1 := by
    intro t
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective t
    rw [hi]
    change QuotientGroup.mk (f ((q : A), (1 : B))) = (1 : (A × B) ⧸ Subgroup.center (A × B))
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨b, hb⟩ := q.property
    change (f (1, b)).1 = (q : A) at hb
    rw [← hb]
    exact hk b
  have ht := CenterQuotients.retract_trivial_of_killed
    (CenterQuotients.quotientMap f hf) (CenterQuotients.quotientMap_surjective f hf) i r hri hkill
  intro b
  let q : Q := (ProductHom.right row).rangeRestrict b
  have hq : q ∈ Subgroup.center Q := (QuotientGroup.eq_one_iff q).mp (ht (QuotientGroup.mk q))
  exact CentralProducts.right_center P Q hc hcover hq
end Kourovka
