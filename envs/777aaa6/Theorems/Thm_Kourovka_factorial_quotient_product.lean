-- Prove2me | Theorems.Thm_Kourovka_factorial_quotient_product
-- name    : Kourovka.factorial_quotient_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:42:32.253982+00:00
-- url     : https://prove2.me/theorems/1bcd9f9f-eac1-43de-bad0-12f3083f54f9
-- title:
--   Kourovka: factorial quotient product
-- statement:
--   One factorial power induces a product of epimorphisms on the two center quotients.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/QuotientProducts.lean#L109-L120
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/QuotientProducts.lean#L109-L120

import Definitions.Def_Kourovka_EventualCentrality
import Definitions.Def_Kourovka_QuotientProducts
import Theorems.Thm_Kourovka_ProductPaths_iterateHom_surjective

set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.factorial_quotient_product [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    let m := (CenterWeight.weight (A × B)).factorial
    ∃ (u : A ⧸ Subgroup.center A →* A ⧸ Subgroup.center A)
      (v : B ⧸ Subgroup.center B →* B ⧸ Subgroup.center B),
      Function.Surjective u ∧ Function.Surjective v ∧
      ∀ x y, CenterQuotients.quotientMap (ProductPaths.iterateHom f m)
        (ProductPaths.iterateHom_surjective f hf m) (CenterQuotients.productEquiv (x, y)) =
        CenterQuotients.productEquiv (u x, v y) := by sorry
