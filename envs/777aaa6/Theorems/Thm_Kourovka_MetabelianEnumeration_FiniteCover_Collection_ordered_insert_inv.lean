-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_ordered_insert_inv
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.ordered_insert_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:48:21.817497+00:00
-- url     : https://prove2.me/theorems/ed1377d3-d623-4e19-bb98-9e6ffdb4913c
-- title:
--   Collection: ordered insert inv
-- statement:
--   The Collection construction uses the ordered insert inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L211-L229
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L211-L229

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.ordered_insert_inv {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a) (B : Set (Lattice k))
    (hB : Solid B)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hshort : ∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (p : Fin a) (v : Lattice k) (i : Fin k) (hv : v ∈ B) (hvi : lower v i ∈ B) :
    conjugate (A p) (orderedWord t v * (t i)⁻¹) =
      conjugate (A p) (orderedWord t (lower v i)) := by sorry
