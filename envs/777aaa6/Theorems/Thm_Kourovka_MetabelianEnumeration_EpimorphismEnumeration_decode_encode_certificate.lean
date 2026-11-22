-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_EpimorphismEnumeration_decode_encode_certificate
-- name    : Kourovka.MetabelianEnumeration.EpimorphismEnumeration.decode_encode_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:26:35.265099+00:00
-- url     : https://prove2.me/theorems/642c64bc-4c12-4afc-84cf-78e758dd279f
-- title:
--   Epimorphism Enumeration: decode encode certificate
-- statement:
--   Encoding and then decoding recovers the original certificate.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/EpimorphismEnumeration.lean#L78-L80
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/EpimorphismEnumeration.lean#L78-L80

import Definitions.Def_Kourovka_Certificates_EpimorphismSemantics
import Definitions.Def_Kourovka_Enumeration_EnumerationCofinality
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
import Definitions.Def_Kourovka_Enumeration_EpimorphismEnumeration
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_decode_encode_certificate

set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.EpimorphismEnumeration

theorem Kourovka.MetabelianEnumeration.EpimorphismEnumeration.decode_encode_certificate (c : Certificate) :
    decodeCertificate (encodeCertificate c) = c := by sorry
