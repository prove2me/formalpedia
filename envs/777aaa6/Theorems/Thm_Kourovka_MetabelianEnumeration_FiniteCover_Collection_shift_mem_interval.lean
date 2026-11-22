-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shift_mem_interval
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.shift_mem_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:54:09.289564+00:00
-- url     : https://prove2.me/theorems/8e2baae3-de8c-4be2-b72f-5ab150288577
-- title:
--   Collection: shift mem interval
-- statement:
--   The Collection construction uses the shift mem interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L32-L62
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L32-L62

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionFinite
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.shift_mem_interval {k : ℕ} {B : Set (Lattice k)} (hB : Solid B)
    (v : Lattice k) (i : Fin k) (m r : ℤ) (hv : v ∈ B) (hm : shift v i m ∈ B)
    (hr : min 0 m ≤ r) (hr' : r ≤ max 0 m) : shift v i r ∈ B := by sorry
