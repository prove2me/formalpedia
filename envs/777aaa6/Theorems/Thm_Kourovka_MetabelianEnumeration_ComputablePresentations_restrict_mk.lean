-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_restrict_mk
-- name    : Kourovka.MetabelianEnumeration.ComputablePresentations.restrict_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:42:53.901249+00:00
-- url     : https://prove2.me/theorems/8830dc34-0d9d-4dd1-8cd2-fd9651a64dc7
-- title:
--   Computable Presentations: restrict mk
-- statement:
--   The Computable Presentations construction uses the restrict mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L38-L45
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L38-L45

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords

theorem Kourovka.MetabelianEnumeration.ComputablePresentations.restrict_mk (n : ℕ) (w : List (ℕ × Bool)) :
    restrictGenerators n (FreeGroup.mk w) = interpretWord n w := by sorry
