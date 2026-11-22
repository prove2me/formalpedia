-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_metabelian_of_all_ordered_commute
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.metabelian_of_all_ordered_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:55:48.439807+00:00
-- url     : https://prove2.me/theorems/979986fe-f148-4293-8686-80246318c973
-- title:
--   Finite Cover: metabelian of all ordered commute
-- statement:
--   The designated commutators make the quotient by the normal closure
--   abelian, while infinite collection makes that normal closure abelian.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverSoundness.lean#L158-L191
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverSoundness.lean#L158-L191

import Definitions.Def_Kourovka_Collection_CollectionRadius
import Definitions.Def_Kourovka_Covers_CertifiedRadius
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverSoundness
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.metabelian_of_all_ordered_commute {k a : ℕ} (data : Datum k a)
    (t : Fin k → G) (A : Fin a → G)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (data.designated i j))
    (hs : ∀ p q v, Commute (A p) (conjugate (A q) (orderedWord t v)))
    (hgen : Subgroup.closure (Set.range t ∪ Set.range A) = ⊤) : Metabelian G := by sorry
