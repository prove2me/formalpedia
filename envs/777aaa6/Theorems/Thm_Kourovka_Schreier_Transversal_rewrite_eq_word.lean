-- Prove2me | Theorems.Thm_Kourovka_Schreier_Transversal_rewrite_eq_word
-- name    : Kourovka.Schreier.Transversal.rewrite_eq_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:14:41.33072+00:00
-- url     : https://prove2.me/theorems/46cb2757-5334-4d83-9555-5a46b3a2f5bf
-- title:
--   Transversal: rewrite eq word
-- statement:
--   The Transversal construction uses the rewrite eq word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/PathLifting.lean#L126-L128
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/PathLifting.lean#L126-L128

import Definitions.Def_Kourovka_Schreier_Transversal
import Definitions.Def_Kourovka_Schreier_PathLifting
set_option autoImplicit true
open Kourovka Kourovka.Schreier Kourovka.Schreier.Transversal
variable {X : Type*} {L : Subgroup (FreeGroup X)} (S : Transversal L)
variable {H : Type*} [Group H]

theorem Kourovka.Schreier.Transversal.rewrite_eq_word [DecidableEq X] (p w : FreeGroup X) :
    S.rewrite p w = S.rewriteWord p w.toWord := by sorry
