-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_checkData_sound
-- name    : Kourovka.MetabelianEnumeration.ComputableEnumeration.checkData_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:27:42.248889+00:00
-- url     : https://prove2.me/theorems/e9a0fe1d-20cf-40c1-8795-fbd823e80a50
-- title:
--   Computable Enumeration: check Data sound
-- statement:
--   The Computable Enumeration construction uses the check Data sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/EnumerationCorrectness.lean#L22-L32
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/EnumerationCorrectness.lean#L22-L32

import Definitions.Def_Kourovka_Enumeration_EnumerationCofinality
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
import Definitions.Def_Kourovka_Enumeration_EnumerationCorrectness
set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration
open Kourovka.MetabelianEnumeration.ComputableEnumeration

theorem Kourovka.MetabelianEnumeration.ComputableEnumeration.checkData_sound (p : PresentationCode) (c : Certificate)
    (h : checkData p c = true) : WellFormed p ∧ Metabelian (GroupOf p) := by sorry
