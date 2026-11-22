-- Prove2me | Theorems.Thm_Kourovka_Schreier_Transversal_edge_vertex
-- name    : Kourovka.Schreier.Transversal.edge_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:40:35.726079+00:00
-- url     : https://prove2.me/theorems/52044dd1-b06e-43dd-b147-b597bf98d8d5
-- title:
--   Transversal: edge vertex
-- statement:
--   The Transversal construction uses the edge vertex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/Transversal.lean#L69-L72
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/Transversal.lean#L69-L72

import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic
import Definitions.Def_Kourovka_Schreier_Transversal
set_option autoImplicit true
open Kourovka Kourovka.Schreier
variable {X : Type*}
open Kourovka.Schreier.Transversal
variable {L : Subgroup (FreeGroup X)} (S : Transversal L)

theorem Kourovka.Schreier.Transversal.edge_vertex (z : S.Edge) : S.edge z.1.val z.2 = z := by sorry
