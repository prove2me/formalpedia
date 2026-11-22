-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_not_precedes_self
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.not_precedes_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:44:37.5669+00:00
-- url     : https://prove2.me/theorems/eab39e0f-9d47-4b8b-8388-e48c00dfc102
-- title:
--   Collection: not precedes self
-- statement:
--   The Collection construction uses the not precedes self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionGeometry.lean#L84-L85
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionGeometry.lean#L84-L85

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionGeometry
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.not_precedes_self {k : ℕ} (reverse : Bool) (i : Fin k) :
    ¬ precedes reverse i i := by sorry
