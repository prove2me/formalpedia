-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableEpimorphism.checkData_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:07:18.379124+00:00
-- url     : https://prove2.me/submissions/4cd1739f-b741-4595-a621-3fd71013b05b

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_ComputableEpimorphism
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEpimorphism_obligations_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_obligations_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_validMaps_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordCertificates_checkList_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEpimorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
namespace Kourovka.MetabelianEnumeration.ComputableEpimorphism
theorem _root_.solution : Primrec₂ checkData := by
  let d : Primrec (fun p : (PresentationCode × PresentationCode) × Certificate => (p.1, p.2.1)) :=
    Primrec.fst.pair (Primrec.fst.comp Primrec.snd)
  exact Primrec.and.comp (ComputableIsomorphism.validMaps_primrec.decide.comp d)
    (checkList_primrec.comp (obligations_primrec.comp d) (Primrec.snd.comp Primrec.snd))
end Kourovka.MetabelianEnumeration.ComputableEpimorphism
