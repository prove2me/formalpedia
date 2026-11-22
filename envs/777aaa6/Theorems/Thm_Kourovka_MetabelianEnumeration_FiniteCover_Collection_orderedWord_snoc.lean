-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_orderedWord_snoc
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.orderedWord_snoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:48:19.311786+00:00
-- url     : https://prove2.me/theorems/3475e9d9-f8dd-44dd-b889-086b67a27fe1
-- title:
--   Collection: ordered Word snoc
-- statement:
--   The Collection construction uses the ordered Word snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L90-L93
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L90-L93

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.orderedWord_snoc {k : ℕ} (t : Fin (k + 1) → G) (v : Lattice (k + 1)) :
    orderedWord t v = orderedWord (fun i => t i.castSucc) (fun i => v i.castSucc) *
      t (Fin.last k) ^ v (Fin.last k) := by sorry
