-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_substitute_primrec
-- name    : Kourovka.MetabelianEnumeration.NaturalWordSubstitution.substitute_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:46:32.265327+00:00
-- url     : https://prove2.me/theorems/03940d0c-54a4-4b72-b351-37bf62bf1e4f
-- title:
--   Natural Word Substitution: substitute primrec
-- statement:
--   The Natural Word Substitution construction uses the substitute primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/NaturalWordSubstitution.lean#L26-L31
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/NaturalWordSubstitution.lean#L26-L31

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Mathlib.Data.List.GetD
import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordSubstitution
open ComputableWords ComputablePresentations

theorem Kourovka.MetabelianEnumeration.NaturalWordSubstitution.substitute_primrec : Primrec₂ substitute := by sorry
