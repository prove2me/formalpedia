-- Prove2me | Theorems.Thm_Kourovka_central_offDiagonal_iff_quotient_product
-- name    : Kourovka.central_offDiagonal_iff_quotient_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:42:23.693042+00:00
-- url     : https://prove2.me/theorems/1b482227-4096-41f0-8bc6-a04e278e4d6c
-- title:
--   Kourovka: central off Diagonal iff quotient product
-- statement:
--   On the center quotient, preservation of the two factors is equivalent to central mixing.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/QuotientProducts.lean#L71-L106
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/QuotientProducts.lean#L71-L106

import Definitions.Def_Kourovka_EventualCentrality
import Definitions.Def_Kourovka_QuotientProducts
set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.central_offDiagonal_iff_quotient_product (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    ((∀ b : B, (f (1, b)).1 ∈ Subgroup.center A) ∧
      (∀ a : A, (f (a, 1)).2 ∈ Subgroup.center B)) ↔
    ∃ (u : A ⧸ Subgroup.center A →* A ⧸ Subgroup.center A)
      (v : B ⧸ Subgroup.center B →* B ⧸ Subgroup.center B),
      Function.Surjective u ∧ Function.Surjective v ∧
      ∀ x y, CenterQuotients.quotientMap f hf (CenterQuotients.productEquiv (x, y)) =
        CenterQuotients.productEquiv (u x, v y) := by sorry
