-- Prove2me | Theorems.Thm_Kourovka_Schreier_Transversal_rewrite_mk
-- name    : Kourovka.Schreier.Transversal.rewrite_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:14:28.829007+00:00
-- url     : https://prove2.me/theorems/ced3aa2c-1c4d-4545-8747-e0fbe5c3a2c4
-- title:
--   Transversal: rewrite mk
-- statement:
--   The Transversal construction uses the rewrite mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/PathLifting.lean#L123-L124
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/PathLifting.lean#L123-L124

import Definitions.Def_Kourovka_Schreier_Transversal
import Definitions.Def_Kourovka_Schreier_PathLifting
set_option autoImplicit true
open Kourovka Kourovka.Schreier Kourovka.Schreier.Transversal
variable {X : Type*} {L : Subgroup (FreeGroup X)} (S : Transversal L)
variable {H : Type*} [Group H]

theorem Kourovka.Schreier.Transversal.rewrite_mk (p : FreeGroup X) (xs : List (X × Bool)) :
    S.rewrite p (FreeGroup.mk xs) = S.rewriteWord p xs := by sorry

attribute [defeq] Kourovka.Schreier.Transversal.rewrite_mk
