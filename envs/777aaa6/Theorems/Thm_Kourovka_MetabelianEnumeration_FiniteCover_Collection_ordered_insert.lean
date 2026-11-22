-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_ordered_insert
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.ordered_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:46:09.342596+00:00
-- url     : https://prove2.me/theorems/563c2878-0e39-444b-b17b-8eba7e91fd4d
-- title:
--   Collection: ordered insert
-- statement:
--   Insert one positive generator into an ordered conjugating word. Only
--   the original and final lattice points and their coordinatewise sub-boxes
--   are used by the proof.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L136-L199
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L136-L199

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.ordered_insert {a : ℕ} (A : Fin a → G) :
    ∀ {k : ℕ} (t : Fin k → G) (designated : Fin k → Fin k → Fin a)
      (B : Set (Lattice k)),
      Solid B →
      (∀ i j, i < j → rightComm (t i) (t j) = A (designated i j)) →
      (∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v))) →
      ∀ p v i, v ∈ B → raise v i ∈ B →
        conjugate (A p) (orderedWord t v * t i) =
          conjugate (A p) (orderedWord t (raise v i)) := by sorry
