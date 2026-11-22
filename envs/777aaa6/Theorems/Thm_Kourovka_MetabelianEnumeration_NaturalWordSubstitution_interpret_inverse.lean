-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_interpret_inverse
-- name    : Kourovka.MetabelianEnumeration.NaturalWordSubstitution.interpret_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:51:26.122731+00:00
-- url     : https://prove2.me/theorems/46fb8035-992b-4e81-9134-3967714824d5
-- title:
--   Natural Word Substitution: interpret inverse
-- statement:
--   The Natural Word Substitution construction uses the interpret inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/NaturalWordSubstitution.lean#L39-L41
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/NaturalWordSubstitution.lean#L39-L41

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Mathlib.Data.List.GetD
import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordSubstitution
open ComputableWords ComputablePresentations

theorem Kourovka.MetabelianEnumeration.NaturalWordSubstitution.interpret_inverse (n : ℕ) (w : Word) :
    interpretWord n (FreeGroup.invRev w) = (interpretWord n w)⁻¹ := by sorry
