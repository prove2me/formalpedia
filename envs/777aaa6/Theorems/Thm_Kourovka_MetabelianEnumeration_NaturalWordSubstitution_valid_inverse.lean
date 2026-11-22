-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_valid_inverse
-- name    : Kourovka.MetabelianEnumeration.NaturalWordSubstitution.valid_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:51:37.072957+00:00
-- url     : https://prove2.me/theorems/4a7d83e4-530f-436c-843b-6a87ee757195
-- title:
--   Natural Word Substitution: valid inverse
-- statement:
--   The Natural Word Substitution construction uses the valid inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/NaturalWordSubstitution.lean#L79-L84
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/NaturalWordSubstitution.lean#L79-L84

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Mathlib.Data.List.GetD
import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordSubstitution
open ComputableWords ComputablePresentations

theorem Kourovka.MetabelianEnumeration.NaturalWordSubstitution.valid_inverse {n : ℕ} {w : Word} (h : ValidWord n w) :
    ValidWord n (FreeGroup.invRev w) := by sorry
