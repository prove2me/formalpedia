-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_checkTrivial_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputablePresentations.checkTrivial_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:46:24.323415+00:00
-- url     : https://prove2.me/theorems/57ba8108-21d8-4efb-915e-f23bbd4c358f
-- title:
--   Computable Presentations: check Trivial primrec
-- statement:
--   The Computable Presentations construction uses the check Trivial primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L111-L115
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L111-L115

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords

theorem Kourovka.MetabelianEnumeration.ComputablePresentations.checkTrivial_primrec : Primrec₂ checkTrivial := by sorry
