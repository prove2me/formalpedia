-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverData.check_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:13:39.493646+00:00
-- url     : https://prove2.me/submissions/617e5cf4-c324-465f-96c6-b4f6bf29b1e6

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_dimension_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_supports_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_checkMargin_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover
namespace Kourovka.MetabelianEnumeration.ComputableCoverData
theorem _root_.solution : Primrec₂ check :=
  ComputableCone.checkMargin_primrec.comp ((dimension_primrec.comp Primrec.fst).pair Primrec.snd)
    (supports_primrec.comp Primrec.fst)
end Kourovka.MetabelianEnumeration.ComputableCoverData
