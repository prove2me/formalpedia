-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableEpimorphism.checkEpi_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:08:22.249413+00:00
-- url     : https://prove2.me/submissions/cc01845e-e941-45ca-b3de-4780b7868a35

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_ComputableEpimorphism
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEpimorphism_checkData_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_checkData_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEpimorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
namespace Kourovka.MetabelianEnumeration.ComputableEpimorphism
theorem _root_.solution : Primrec₂ checkEpi :=
  checkData_primrec.comp Primrec.fst
    (Primrec.option_getD.comp (Primrec.decode.comp Primrec.snd) (Primrec.const (([], []), [])))
end Kourovka.MetabelianEnumeration.ComputableEpimorphism
