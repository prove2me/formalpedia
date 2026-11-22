-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_ordered_append_inv_pow
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.ordered_append_inv_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:54:12.561577+00:00
-- url     : https://prove2.me/theorems/c03055db-0e06-41c1-97d9-486189a86925
-- title:
--   Collection: ordered append inv pow
-- statement:
--   The Collection construction uses the ordered append inv pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L93-L110
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L93-L110

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionFinite
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
variable {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
  (designated : Fin k → Fin k → Fin a) (B : Set (Lattice k))
  (hB : Solid B)
  (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
  (hs : ∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v)))
include hB ht hs

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.ordered_append_inv_pow (p : Fin a) (v : Lattice k) (i : Fin k) (n : ℕ)
    (h : ∀ r : ℕ, r ≤ n → shift v i (-(r : ℤ)) ∈ B) :
    conjugate (A p) (orderedWord t v * (t i)⁻¹ ^ n) =
      conjugate (A p) (orderedWord t (shift v i (-(n : ℤ)))) := by sorry
