-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_validInput_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputablePresentations.validInput_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:51:12.777789+00:00
-- url     : https://prove2.me/theorems/9370ece2-78a0-4fb3-955f-7a7865bd8010
-- title:
--   Computable Presentations: valid Input primrec
-- statement:
--   The Computable Presentations construction uses the valid Input primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L101-L105
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L101-L105

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords

theorem Kourovka.MetabelianEnumeration.ComputablePresentations.validInput_primrec : PrimrecPred validInput := by sorry
