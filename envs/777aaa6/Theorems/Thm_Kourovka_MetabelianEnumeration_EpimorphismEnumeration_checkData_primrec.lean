-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_EpimorphismEnumeration_checkData_primrec
-- name    : Kourovka.MetabelianEnumeration.EpimorphismEnumeration.checkData_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:26:35.347222+00:00
-- url     : https://prove2.me/theorems/939d6dcc-47ed-4035-b1ad-5154b982f143
-- title:
--   Epimorphism Enumeration: check Data primrec
-- statement:
--   Every component of the structured certificate check is primitive recursive.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/EpimorphismEnumeration.lean#L48-L59
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/EpimorphismEnumeration.lean#L48-L59

import Definitions.Def_Kourovka_Certificates_EpimorphismSemantics
import Definitions.Def_Kourovka_Enumeration_EnumerationCofinality
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
import Definitions.Def_Kourovka_Enumeration_EpimorphismEnumeration
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_checkData_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEpimorphism_checkData_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_checkData_primrec

set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.EpimorphismEnumeration

theorem Kourovka.MetabelianEnumeration.EpimorphismEnumeration.checkData_primrec : Primrec₂ checkData := by sorry
