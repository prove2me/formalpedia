-- Prove2me | Theorems.Thm_Kourovka_central_offDiagonal_factorial_iterate
-- name    : Kourovka.central_offDiagonal_factorial_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:34:50.597406+00:00
-- url     : https://prove2.me/theorems/17c6ed0b-7ae8-46dd-aafb-ebc44bb70abd
-- title:
--   Kourovka: central off Diagonal factorial iterate
-- statement:
--   The factorial of the product's weight centralizes the off-diagonal components
--       of every surjective endomorphism of that product.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/EventualCentrality.lean#L84-L101
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/EventualCentrality.lean#L84-L101

import Definitions.Def_Kourovka_MixedPaths
import Definitions.Def_Kourovka_CenterQuotients
import Definitions.Def_Kourovka_EventualCentrality
set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.central_offDiagonal_factorial_iterate [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    let m := (CenterWeight.weight (A × B)).factorial
    (∀ b : B, (ProductPaths.iterateHom f m (1, b)).1 ∈ Subgroup.center A) ∧
      (∀ a : A, (ProductPaths.iterateHom f m (a, 1)).2 ∈ Subgroup.center B) := by sorry
