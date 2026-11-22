-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_interpret_singleton_false
-- name    : Kourovka.MetabelianEnumeration.NaturalWordSubstitution.interpret_singleton_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:45:34.36798+00:00
-- url     : https://prove2.me/theorems/ea7ee19b-bdaa-42e6-9d19-7f55f5972938
-- title:
--   Natural Word Substitution: interpret singleton false
-- statement:
--   The Natural Word Substitution construction uses the interpret singleton false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/NaturalWordSubstitution.lean#L101-L103
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/NaturalWordSubstitution.lean#L101-L103

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Mathlib.Data.List.GetD
import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordSubstitution
open ComputableWords ComputablePresentations

theorem Kourovka.MetabelianEnumeration.NaturalWordSubstitution.interpret_singleton_false (n i : ℕ) (hi : i < n) :
    interpretWord n [(i, false)] = (FreeGroup.of ⟨i, hi⟩)⁻¹ := by sorry
