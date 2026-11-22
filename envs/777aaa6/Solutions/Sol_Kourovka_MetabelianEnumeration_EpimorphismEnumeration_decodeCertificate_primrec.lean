-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.EpimorphismEnumeration.decodeCertificate_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:26:34.949896+00:00
-- url     : https://prove2.me/submissions/2affa022-4231-4a7b-84e7-10d298c8d668

import Definitions.Def_Kourovka_Certificates_EpimorphismSemantics
import Definitions.Def_Kourovka_Enumeration_EnumerationCofinality
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
import Definitions.Def_Kourovka_Enumeration_EpimorphismEnumeration
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_decodeDefault_primrec


set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.EpimorphismEnumeration
namespace Kourovka.MetabelianEnumeration.EpimorphismEnumeration
theorem _root_.solution : Primrec decodeCertificate :=
  ComputableEnumeration.decodeDefault_primrec defaultCertificate
end Kourovka.MetabelianEnumeration.EpimorphismEnumeration
