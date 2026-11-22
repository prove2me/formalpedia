-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_mem_normalizer_of_conjugate
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.mem_normalizer_of_conjugate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:54:02.667717+00:00
-- url     : https://prove2.me/theorems/179fd1ed-7a44-46e4-8d77-f01cc8953af7
-- title:
--   Collection: mem normalizer of conjugate
-- statement:
--   The Collection construction uses the mem normalizer of conjugate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L244-L253
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L244-L253

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.mem_normalizer_of_conjugate {H : Subgroup G} {g : G}
    (hg : ∀ x ∈ H, conjugate x g ∈ H)
    (hi : ∀ x ∈ H, conjugate x g⁻¹ ∈ H) : g ∈ H.normalizer := by sorry
