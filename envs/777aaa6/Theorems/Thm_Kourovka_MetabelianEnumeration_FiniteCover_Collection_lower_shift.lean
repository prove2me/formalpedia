-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_lower_shift
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.lower_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:44:49.036809+00:00
-- url     : https://prove2.me/theorems/9a177a3e-fa40-43e1-ad3a-79e89b64ad88
-- title:
--   Collection: lower shift
-- statement:
--   The Collection construction uses the lower shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L28-L30
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L28-L30

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionFinite
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.lower_shift {k : ℕ} (v : Lattice k) (i : Fin k) (m : ℤ) :
    lower (shift v i m) i = shift v i (m - 1) := by sorry
