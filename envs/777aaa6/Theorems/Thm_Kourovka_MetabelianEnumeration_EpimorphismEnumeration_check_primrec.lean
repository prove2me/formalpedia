-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_EpimorphismEnumeration_check_primrec
-- name    : Kourovka.MetabelianEnumeration.EpimorphismEnumeration.check_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:26:14.833545+00:00
-- url     : https://prove2.me/theorems/e4bf7aa2-3d15-4260-9a24-8f74de497bb9
-- title:
--   Epimorphism Enumeration: check primrec
-- statement:
--   The two-input Boolean predicate of Theorem 1.1 is primitive recursive.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/EpimorphismEnumeration.lean#L86-L88
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/EpimorphismEnumeration.lean#L86-L88

import Definitions.Def_Kourovka_Certificates_EpimorphismSemantics
import Definitions.Def_Kourovka_Enumeration_EnumerationCofinality
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
import Definitions.Def_Kourovka_Enumeration_EpimorphismEnumeration
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_check_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_check_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_check_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_check_primrec

set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.EpimorphismEnumeration

theorem Kourovka.MetabelianEnumeration.EpimorphismEnumeration.check_primrec : Primrec₂ check := by sorry
