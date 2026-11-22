-- Prove2me | Theorems.Thm_Kourovka_Schreier_Transversal_lift_edgeValue
-- name    : Kourovka.Schreier.Transversal.lift_edgeValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:14:28.978966+00:00
-- url     : https://prove2.me/theorems/22242be3-16d5-4fa6-89c6-79dec491f1b8
-- title:
--   Transversal: lift edge Value
-- statement:
--   Evaluating lifted edges telescopes to the initial section, word, and final section.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/PathLifting.lean#L131-L140
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/PathLifting.lean#L131-L140

import Definitions.Def_Kourovka_Schreier_Transversal
import Definitions.Def_Kourovka_Schreier_PathLifting
set_option autoImplicit true
open Kourovka Kourovka.Schreier Kourovka.Schreier.Transversal
variable {X : Type*} {L : Subgroup (FreeGroup X)} (S : Transversal L)
variable {H : Type*} [Group H]

theorem Kourovka.Schreier.Transversal.lift_edgeValue (p w : FreeGroup X) :
    S.lift S.edgeValue p w = S.rep p * w * (S.rep (p * w))⁻¹ := by sorry
