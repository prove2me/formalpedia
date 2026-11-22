-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_orderedWord_tail_prefix
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.orderedWord_tail_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:55:16.666614+00:00
-- url     : https://prove2.me/theorems/13056ee6-a6e5-4d29-b168-52f0001cf507
-- title:
--   Collection: ordered Word tail prefix
-- statement:
--   The Collection construction uses the ordered Word tail prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionRadius.lean#L90-L107
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionRadius.lean#L90-L107

import Definitions.Def_Kourovka_Collection_CollectionFinite
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Collection_CollectionRadius
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.orderedWord_tail_prefix {k : ℕ} (t : Fin k → G) (v : Lattice k) (j : Fin k) :
    orderedWord t v = orderedWord t (tailStep true v j) *
      orderedWord t (prefixStep true v j) := by sorry
