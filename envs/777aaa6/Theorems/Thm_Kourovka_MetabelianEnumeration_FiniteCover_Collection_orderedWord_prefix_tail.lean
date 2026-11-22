-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_orderedWord_prefix_tail
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.orderedWord_prefix_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:55:17.525721+00:00
-- url     : https://prove2.me/theorems/7dfccf8b-7288-4362-bbd4-5e696b648ba6
-- title:
--   Collection: ordered Word prefix tail
-- statement:
--   The Collection construction uses the ordered Word prefix tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionRadius.lean#L84-L88
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionRadius.lean#L84-L88

import Definitions.Def_Kourovka_Collection_CollectionFinite
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Collection_CollectionRadius
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.orderedWord_prefix_tail {k : ℕ} (t : Fin k → G) (v : Lattice k) (j : Fin k) :
    orderedWord t v = orderedWord t (prefixStep false v j) *
      orderedWord t (tailStep false v j) := by sorry
