-- Prove2me | Theorems.Thm_Kourovka_quotient_product_of_central_offDiagonal
-- name    : Kourovka.quotient_product_of_central_offDiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:35:24.49776+00:00
-- url     : https://prove2.me/theorems/be985b75-b97e-4828-8469-26354bb4ab44
-- title:
--   Kourovka: quotient product of central off Diagonal
-- statement:
--   Central off-diagonal images give a product of epimorphisms on the center quotients.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/QuotientProducts.lean#L11-L68
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/QuotientProducts.lean#L11-L68

import Definitions.Def_Kourovka_EventualCentrality
import Definitions.Def_Kourovka_QuotientProducts
set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.quotient_product_of_central_offDiagonal (f : A × B →* A × B)
    (hf : Function.Surjective f)
    (h12 : ∀ b : B, (f (1, b)).1 ∈ Subgroup.center A)
    (h21 : ∀ a : A, (f (a, 1)).2 ∈ Subgroup.center B) :
    ∃ (u : A ⧸ Subgroup.center A →* A ⧸ Subgroup.center A)
      (v : B ⧸ Subgroup.center B →* B ⧸ Subgroup.center B),
      Function.Surjective u ∧ Function.Surjective v ∧
      ∀ x y, CenterQuotients.quotientMap f hf (CenterQuotients.productEquiv (x, y)) =
        CenterQuotients.productEquiv (u x, v y) := by sorry
