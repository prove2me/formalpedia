-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_zpow_mul
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_zpow_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:53:52.838991+00:00
-- url     : https://prove2.me/theorems/4c5fb634-cd67-48c8-aa3c-08db59cfcd3a
-- title:
--   Collection: conjugate zpow mul
-- statement:
--   The Collection construction uses the conjugate zpow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L72-L88
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L72-L88

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_zpow_mul (x t c : G) (m : ℤ)
    (h : ∀ r : ℤ, |r| ≤ |m| → Commute c (conjugate x (t ^ r))) :
    conjugate x ((t * c) ^ m) = conjugate x (t ^ m) := by sorry
