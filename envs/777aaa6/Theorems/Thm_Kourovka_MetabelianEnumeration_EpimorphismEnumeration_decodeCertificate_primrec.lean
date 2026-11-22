-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_EpimorphismEnumeration_decodeCertificate_primrec
-- name    : Kourovka.MetabelianEnumeration.EpimorphismEnumeration.decodeCertificate_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:26:27.087708+00:00
-- url     : https://prove2.me/theorems/e951a335-ac76-49f8-99d0-b3431223d41b
-- title:
--   Epimorphism Enumeration: decode Certificate primrec
-- statement:
--   Total decoding preserves primitive recursiveness.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/EpimorphismEnumeration.lean#L74-L75
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/EpimorphismEnumeration.lean#L74-L75

import Definitions.Def_Kourovka_Certificates_EpimorphismSemantics
import Definitions.Def_Kourovka_Enumeration_EnumerationCofinality
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
import Definitions.Def_Kourovka_Enumeration_EpimorphismEnumeration
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_decodeCertificate_primrec

set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.EpimorphismEnumeration

theorem Kourovka.MetabelianEnumeration.EpimorphismEnumeration.decodeCertificate_primrec : Primrec decodeCertificate := by sorry
