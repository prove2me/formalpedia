-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIsomorphism.checkIso_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:06:56.366086+00:00
-- url     : https://prove2.me/submissions/7c5bbd26-7bd7-4645-89f3-50670ed98db2

import Definitions.Def_Kourovka_Certificates_NaturalWordCertificates
import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_checkData_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
namespace Kourovka.MetabelianEnumeration.ComputableIsomorphism
theorem _root_.solution : Primrec₂ checkIso :=
  checkData_primrec.comp Primrec.fst
    (Primrec.option_getD.comp (Primrec.decode.comp Primrec.snd) (Primrec.const (([], []), [])))
end Kourovka.MetabelianEnumeration.ComputableIsomorphism
