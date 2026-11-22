-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_checkTrivial_correct
-- name    : Kourovka.MetabelianEnumeration.ComputablePresentations.checkTrivial_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:46:28.689091+00:00
-- url     : https://prove2.me/theorems/11abfb69-8a7a-461b-8b57-124c526874ce
-- title:
--   Computable Presentations: check Trivial correct
-- statement:
--   The Computable Presentations construction uses the check Trivial correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L117-L127
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L117-L127

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords

theorem Kourovka.MetabelianEnumeration.ComputablePresentations.checkTrivial_correct (input : PresentationCode × List (ℕ × Bool)) :
    (∃ certificate, checkTrivial input certificate = true) ↔
      validInput input ∧
        PresentedGroup.mk (relations input.1) (interpretWord input.1.1 input.2) = 1 := by sorry
