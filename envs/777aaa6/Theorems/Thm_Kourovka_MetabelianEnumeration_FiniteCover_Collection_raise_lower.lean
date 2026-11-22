-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_lower
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:44:08.939169+00:00
-- url     : https://prove2.me/theorems/117bd064-2de1-4205-be00-ba0a518cbc8c
-- title:
--   Collection: raise lower
-- statement:
--   The Collection construction uses the raise lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L204-L209
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L204-L209

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_lower {k : ℕ} (v : Lattice k) (i : Fin k) :
    raise (lower v i) i = v := by sorry
