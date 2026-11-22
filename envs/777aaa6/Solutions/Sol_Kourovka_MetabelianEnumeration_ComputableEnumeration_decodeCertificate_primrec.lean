-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableEnumeration.decodeCertificate_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:57:52.807056+00:00
-- url     : https://prove2.me/submissions/84fcbbbf-f02c-41ba-bd53-5de96eacb7c4

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Presentations_QuotientCodes
import Definitions.Def_Kourovka_Enumeration_ComputableEnumeration
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_decodeDefault_primrec

set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEnumeration
namespace Kourovka.MetabelianEnumeration.ComputableEnumeration
theorem _root_.solution : Primrec decodeCertificate :=
  decodeDefault_primrec defaultCertificate
end Kourovka.MetabelianEnumeration.ComputableEnumeration
