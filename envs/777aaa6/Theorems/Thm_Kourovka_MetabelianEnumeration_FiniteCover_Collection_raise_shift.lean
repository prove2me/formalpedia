-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_shift
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:45:04.865647+00:00
-- url     : https://prove2.me/theorems/f4e5e1ec-4148-4c7e-b932-62fa133a21b2
-- title:
--   Collection: raise shift
-- statement:
--   The Collection construction uses the raise shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L24-L26
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L24-L26

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionFinite
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_shift {k : ℕ} (v : Lattice k) (i : Fin k) (m : ℤ) :
    raise (shift v i m) i = shift v i (m + 1) := by sorry
