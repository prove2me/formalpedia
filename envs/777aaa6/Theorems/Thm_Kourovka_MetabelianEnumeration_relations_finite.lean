-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_relations_finite
-- name    : Kourovka.MetabelianEnumeration.relations_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:59:59.708263+00:00
-- url     : https://prove2.me/theorems/a352cf84-3e4a-4fbc-923f-d0a4d37fa4fb
-- title:
--   Metabelian Enumeration: relations finite
-- statement:
--   The Metabelian Enumeration construction uses the relations finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/Presentations.lean#L43-L44
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/Presentations.lean#L43-L44

import Definitions.Def_Kourovka_Computability_Enumeration
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Commutator.Basic
import Definitions.Def_Kourovka_Presentations_Presentations
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration

theorem Kourovka.MetabelianEnumeration.relations_finite (p : PresentationCode) : (relations p).Finite := by sorry
