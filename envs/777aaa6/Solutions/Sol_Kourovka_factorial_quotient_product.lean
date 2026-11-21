-- Prove2me | solution 1 for Kourovka.factorial_quotient_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:46:58.499198+00:00
-- url     : https://prove2.me/submissions/36d28396-2dd2-4840-aa2f-29851f82dccf

import Definitions.Def_Kourovka_EventualCentrality
import Definitions.Def_Kourovka_QuotientProducts
import Theorems.Thm_Kourovka_quotient_product_of_central_offDiagonal
import Theorems.Thm_Kourovka_ProductPaths_iterateHom_surjective
import Theorems.Thm_Kourovka_central_offDiagonal_factorial_iterate


set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka
theorem _root_.solution [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    let m := (CenterWeight.weight (A × B)).factorial
    ∃ (u : A ⧸ Subgroup.center A →* A ⧸ Subgroup.center A)
      (v : B ⧸ Subgroup.center B →* B ⧸ Subgroup.center B),
      Function.Surjective u ∧ Function.Surjective v ∧
      ∀ x y, CenterQuotients.quotientMap (ProductPaths.iterateHom f m)
        (ProductPaths.iterateHom_surjective f hf m) (CenterQuotients.productEquiv (x, y)) =
        CenterQuotients.productEquiv (u x, v y) := by
  obtain ⟨h12, h21⟩ := central_offDiagonal_factorial_iterate f hf
  exact quotient_product_of_central_offDiagonal _ (ProductPaths.iterateHom_surjective f hf _) h12 h21
end Kourovka
