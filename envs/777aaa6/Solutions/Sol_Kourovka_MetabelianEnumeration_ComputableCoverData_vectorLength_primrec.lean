-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverData.vectorLength_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:07:47.411184+00:00
-- url     : https://prove2.me/submissions/391004c7-3c08-4ba0-bb9a-e135ee8bab4f

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_nat_sum_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_natAbs_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover
namespace Kourovka.MetabelianEnumeration.ComputableCoverData
theorem _root_.solution : Primrec₂ vectorLength :=
  nat_sum_primrec.comp (Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (natAbs_primrec.comp ((Primrec.list_getD 0).comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂)
end Kourovka.MetabelianEnumeration.ComputableCoverData
