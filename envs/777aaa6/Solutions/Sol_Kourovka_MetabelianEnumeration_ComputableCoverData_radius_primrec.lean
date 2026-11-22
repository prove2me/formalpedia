-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverData.radius_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:10:25.019505+00:00
-- url     : https://prove2.me/submissions/4076db68-c587-483e-89fb-a7cb297c8510

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_dimension_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_lengthBound_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_nat_pow_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover
namespace Kourovka.MetabelianEnumeration.ComputableCoverData
theorem _root_.solution : Primrec₂ radius :=
  Primrec.nat_add.comp (Primrec.const 1) (Primrec.nat_mul.comp
    (Primrec.nat_mul.comp (Primrec.const 2) (dimension_primrec.comp Primrec.fst))
    (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 1) (lengthBound_primrec.comp Primrec.fst))
      (Primrec.nat_mul.comp
        (Primrec.nat_mul.comp
          (nat_pow_primrec.comp (lengthBound_primrec.comp Primrec.fst) (Primrec.const 2))
          (dimension_primrec.comp Primrec.fst))
        (nat_pow_primrec.comp (Primrec.const 2) Primrec.snd))))
end Kourovka.MetabelianEnumeration.ComputableCoverData
