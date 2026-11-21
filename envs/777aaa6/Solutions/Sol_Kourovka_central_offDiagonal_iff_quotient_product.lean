-- Prove2me | solution 1 for Kourovka.central_offDiagonal_iff_quotient_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:42:50.489144+00:00
-- url     : https://prove2.me/submissions/973293f3-6938-4aab-8461-b7458d2ace56

import Definitions.Def_Kourovka_EventualCentrality
import Definitions.Def_Kourovka_QuotientProducts
import Theorems.Thm_Kourovka_quotient_product_of_central_offDiagonal
import Theorems.Thm_Kourovka_CenterQuotients_productEquiv_mk
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
    (hf : Function.Surjective f) :
    ((∀ b : B, (f (1, b)).1 ∈ Subgroup.center A) ∧
      (∀ a : A, (f (a, 1)).2 ∈ Subgroup.center B)) ↔
    ∃ (u : A ⧸ Subgroup.center A →* A ⧸ Subgroup.center A)
      (v : B ⧸ Subgroup.center B →* B ⧸ Subgroup.center B),
      Function.Surjective u ∧ Function.Surjective v ∧
      ∀ x y, CenterQuotients.quotientMap f hf (CenterQuotients.productEquiv (x, y)) =
        CenterQuotients.productEquiv (u x, v y) := by
  constructor
  · rintro ⟨h12, h21⟩
    exact quotient_product_of_central_offDiagonal f hf h12 h21
  · rintro ⟨u, v, _, _, h⟩
    let E := CenterQuotients.productEquiv (A := A) (B := B)
    have hmk (a : A) (b : B) : E.symm (QuotientGroup.mk (a, b)) =
        (QuotientGroup.mk a, QuotientGroup.mk b) := by
      apply E.injective
      rw [E.apply_symm_apply]
      exact (CenterQuotients.productEquiv_mk a b).symm
    constructor
    · intro b
      have he := h (QuotientGroup.mk (1 : A)) (QuotientGroup.mk b)
      rw [CenterQuotients.productEquiv_mk] at he
      change QuotientGroup.mk (f (1, b)) = E (u (QuotientGroup.mk 1), v (QuotientGroup.mk b)) at he
      have ht := congrArg E.symm he
      rw [hmk, E.symm_apply_apply] at ht
      apply (QuotientGroup.eq_one_iff _).mp
      simpa only [QuotientGroup.mk_one, map_one] using congrArg Prod.fst ht
    · intro a
      have he := h (QuotientGroup.mk a) (QuotientGroup.mk (1 : B))
      rw [CenterQuotients.productEquiv_mk] at he
      change QuotientGroup.mk (f (a, 1)) = E (u (QuotientGroup.mk a), v (QuotientGroup.mk 1)) at he
      have ht := congrArg E.symm he
      rw [hmk, E.symm_apply_apply] at ht
      apply (QuotientGroup.eq_one_iff _).mp
      simpa only [QuotientGroup.mk_one, map_one] using congrArg Prod.snd ht
end Kourovka
