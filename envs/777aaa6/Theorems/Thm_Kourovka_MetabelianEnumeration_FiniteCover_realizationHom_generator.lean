-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_realizationHom_generator
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.realizationHom_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:53:39.406312+00:00
-- url     : https://prove2.me/theorems/ef367655-0b60-463e-afeb-039dc4730d5b
-- title:
--   Finite Cover: realization Hom generator
-- statement:
--   The Finite Cover construction uses the realization Hom generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/FiniteCover.lean#L196-L200
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/FiniteCover.lean#L196-L200

import Definitions.Def_Kourovka_Polyhedral_ConeMargin
import Definitions.Def_Kourovka_Presentations_FiniteQuotient
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex
import Definitions.Def_Kourovka_Covers_FiniteCover
set_option autoImplicit true
attribute [-instance] instConditionallyCompleteLinearOrder
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover

theorem Kourovka.MetabelianEnumeration.FiniteCover.realizationHom_generator {k a : ℕ} (data : Datum k a) (radius : ℕ)
    {G : Type*} [Group G] (t : Fin k → G) (A : Fin a → G)
    (h : Realizes data radius t A) (i : Fin (k + a)) :
    realizationHom data radius t A h (PresentedGroup.of i) = generatorAssignment t A i := by sorry
