-- Prove2me | Theorems.Thm_Kourovka_Schreier_Transversal_evaluate_rewrite
-- name    : Kourovka.Schreier.Transversal.evaluate_rewrite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:14:43.521095+00:00
-- url     : https://prove2.me/theorems/1ee9e015-1c14-4c06-8289-5f0eb55f4ecc
-- title:
--   Transversal: evaluate rewrite
-- statement:
--   Evaluation of rewritten words recovers their subgroup correction.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/PathLifting.lean#L143-L147
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/PathLifting.lean#L143-L147

import Definitions.Def_Kourovka_Schreier_Transversal
import Definitions.Def_Kourovka_Schreier_PathLifting
set_option autoImplicit true
open Kourovka Kourovka.Schreier Kourovka.Schreier.Transversal
variable {X : Type*} {L : Subgroup (FreeGroup X)} (S : Transversal L)
variable {H : Type*} [Group H]

theorem Kourovka.Schreier.Transversal.evaluate_rewrite (p w : FreeGroup X) :
    (S.evaluate (S.rewrite p w)).val = S.rep p * w * (S.rep (p * w))⁻¹ := by sorry
