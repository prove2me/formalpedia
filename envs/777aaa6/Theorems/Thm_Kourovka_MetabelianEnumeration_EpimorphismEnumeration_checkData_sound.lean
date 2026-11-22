-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_EpimorphismEnumeration_checkData_sound
-- name    : Kourovka.MetabelianEnumeration.EpimorphismEnumeration.checkData_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:26:28.923031+00:00
-- url     : https://prove2.me/theorems/b1a1aa09-3718-41e3-a599-f157df360c1c
-- title:
--   Epimorphism Enumeration: check Data sound
-- statement:
--   Soundness: an accepted certificate defines a metabelian group.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/EpimorphismEnumeration.lean#L91-L101
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/EpimorphismEnumeration.lean#L91-L101

import Definitions.Def_Kourovka_Certificates_EpimorphismSemantics
import Definitions.Def_Kourovka_Enumeration_EnumerationCofinality
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
import Definitions.Def_Kourovka_Enumeration_EpimorphismEnumeration
set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.EpimorphismEnumeration

theorem Kourovka.MetabelianEnumeration.EpimorphismEnumeration.checkData_sound (p : PresentationCode) (c : Certificate)
    (h : checkData p c = true) : WellFormed p ∧ Metabelian (GroupOf p) := by sorry
