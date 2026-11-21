-- Prove2me | Theorems.Thm_Kourovka_first_offDiagonal_central_of_killed
-- name    : Kourovka.first_offDiagonal_central_of_killed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:34:56.808654+00:00
-- url     : https://prove2.me/theorems/fcf36dbe-f256-44fa-8a1d-6d567a0b6028
-- title:
--   Kourovka: first off Diagonal central of killed
-- statement:
--   An off-diagonal image killed modulo the product center must itself be central.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/EventualCentrality.lean#L13-L67
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/EventualCentrality.lean#L13-L67

import Definitions.Def_Kourovka_MixedPaths
import Definitions.Def_Kourovka_CenterQuotients
import Definitions.Def_Kourovka_EventualCentrality
set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.first_offDiagonal_central_of_killed [Group.FG A] [Group.FG B] [IsSolvable A]
    (f : A × B →* A × B) (hf : Function.Surjective f)
    (hk : ∀ b : B, f ((f (1, b)).1, 1) ∈ Subgroup.center (A × B)) :
    ∀ b : B, (f (1, b)).1 ∈ Subgroup.center A := by sorry
