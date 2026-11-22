-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_check_correct
-- name    : Kourovka.MetabelianEnumeration.ComputableEnumeration.check_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:27:13.475644+00:00
-- url     : https://prove2.me/theorems/28ab33ae-1843-480d-96c7-a66a60630f0d
-- title:
--   Computable Enumeration: check correct
-- statement:
--   The Computable Enumeration construction uses the check correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/EnumerationCorrectness.lean#L52-L58
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/EnumerationCorrectness.lean#L52-L58

import Definitions.Def_Kourovka_Enumeration_EnumerationCofinality
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
import Definitions.Def_Kourovka_Enumeration_EnumerationCorrectness
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_check_correct
import Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_check_correct

set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration
open Kourovka.MetabelianEnumeration.ComputableEnumeration

theorem Kourovka.MetabelianEnumeration.ComputableEnumeration.check_correct (p : ℕ) : DefinesMetabelian p ↔ ∃ c, check p c = true := by sorry
