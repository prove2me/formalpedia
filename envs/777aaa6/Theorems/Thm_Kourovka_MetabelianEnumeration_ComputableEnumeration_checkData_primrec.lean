-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_checkData_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableEnumeration.checkData_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:07:32.984195+00:00
-- url     : https://prove2.me/theorems/fa18a5a0-b85e-492d-94e8-0b298ecb88ec
-- title:
--   Computable Enumeration: check Data primrec
-- statement:
--   The Computable Enumeration construction uses the check Data primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/ComputableEnumeration.lean#L46-L58
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/ComputableEnumeration.lean#L46-L58

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Presentations_QuotientCodes
import Definitions.Def_Kourovka_Enumeration_ComputableEnumeration
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_checkData_primrec

set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEnumeration

theorem Kourovka.MetabelianEnumeration.ComputableEnumeration.checkData_primrec : Primrec₂ checkData := by sorry
