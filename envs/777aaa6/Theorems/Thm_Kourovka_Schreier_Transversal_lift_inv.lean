-- Prove2me | Theorems.Thm_Kourovka_Schreier_Transversal_lift_inv
-- name    : Kourovka.Schreier.Transversal.lift_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:14:26.122735+00:00
-- url     : https://prove2.me/theorems/87e4e2a4-9cc4-4228-8af6-3045f46be58f
-- title:
--   Transversal: lift inv
-- statement:
--   Reversing a path inverts its lifted label.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/PathLifting.lean#L99-L104
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/PathLifting.lean#L99-L104

import Definitions.Def_Kourovka_Schreier_Transversal
import Definitions.Def_Kourovka_Schreier_PathLifting
set_option autoImplicit true
open Kourovka Kourovka.Schreier Kourovka.Schreier.Transversal
variable {X : Type*} {L : Subgroup (FreeGroup X)} (S : Transversal L)
variable {H : Type*} [Group H]

theorem Kourovka.Schreier.Transversal.lift_inv (f : S.Edge → H) (p w : FreeGroup X) :
    S.lift f (p * w) w⁻¹ = (S.lift f p w)⁻¹ := by sorry
