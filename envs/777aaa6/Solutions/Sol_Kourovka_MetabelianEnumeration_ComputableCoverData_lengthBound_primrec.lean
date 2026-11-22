-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverData.lengthBound_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:09:05.843197+00:00
-- url     : https://prove2.me/submissions/e66fdf0d-d7ba-4100-8f04-251b3b561c77

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_dimension_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_nat_sum_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_vectorLength_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover
namespace Kourovka.MetabelianEnumeration.ComputableCoverData
theorem _root_.solution : Primrec lengthBound :=
  Primrec.nat_add.comp (Primrec.const 1) (nat_sum_primrec.comp
    (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd)
      (Primrec.list_map (Primrec.snd.comp Primrec.snd)
        (vectorLength_primrec.comp (dimension_primrec.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd)).to₂).to₂))
end Kourovka.MetabelianEnumeration.ComputableCoverData
