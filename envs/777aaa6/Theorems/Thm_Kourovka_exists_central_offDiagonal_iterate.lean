-- Prove2me | Theorems.Thm_Kourovka_exists_central_offDiagonal_iterate
-- name    : Kourovka.exists_central_offDiagonal_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:35:50.895349+00:00
-- url     : https://prove2.me/theorems/89d3d3d8-3068-4358-95d8-cad8b29d5995
-- title:
--   Kourovka: exists central off Diagonal iterate
-- statement:
--   A surjective endomorphism of a product of finitely generated soluble groups has
--       a positive iterate whose off-diagonal components are central.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/EventualCentrality.lean#L105-L112
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/EventualCentrality.lean#L105-L112

import Definitions.Def_Kourovka_MixedPaths
import Definitions.Def_Kourovka_CenterQuotients
import Definitions.Def_Kourovka_EventualCentrality
set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.exists_central_offDiagonal_iterate [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    ∃ m : ℕ, 0 < m ∧
      (∀ b : B, (ProductPaths.iterateHom f m (1, b)).1 ∈ Subgroup.center A) ∧
      (∀ a : A, (ProductPaths.iterateHom f m (a, 1)).2 ∈ Subgroup.center B) := by sorry
