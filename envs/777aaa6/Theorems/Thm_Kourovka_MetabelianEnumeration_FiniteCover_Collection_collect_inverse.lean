-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_collect_inverse
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.collect_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:48:52.422539+00:00
-- url     : https://prove2.me/theorems/5a22e111-300c-4439-aba1-017d2c6a805c
-- title:
--   Collection: collect inverse
-- statement:
--   The Collection construction uses the collect inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionRadius.lean#L109-L117
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionRadius.lean#L109-L117

import Definitions.Def_Kourovka_Collection_CollectionFinite
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Collection_CollectionRadius
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.collect_inverse {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a) (B : Set (Lattice k))
    (hB : Solid B)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hs : ∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (p : Fin a) (v : Lattice k) (hv : v ∈ B) :
    conjugate (A p) (orderedWord t v)⁻¹ = conjugate (A p) (orderedWord t (-v)) := by sorry
