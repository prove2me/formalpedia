-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIsomorphism.checkData_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:05:53.077218+00:00
-- url     : https://prove2.me/submissions/90c424fd-9083-41e7-96b6-5271f80f692b

import Definitions.Def_Kourovka_Certificates_NaturalWordCertificates
import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_validMaps_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_obligations_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordCertificates_checkList_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
namespace Kourovka.MetabelianEnumeration.ComputableIsomorphism
theorem _root_.solution : Primrec₂ checkData := by
  let d : Primrec (fun p : (PresentationCode × PresentationCode) × Certificate => (p.1, p.2.1)) :=
    Primrec.fst.pair (Primrec.fst.comp Primrec.snd)
  exact Primrec.and.comp (validMaps_primrec.decide.comp d)
    (checkList_primrec.comp (obligations_primrec.comp d) (Primrec.snd.comp Primrec.snd))
end Kourovka.MetabelianEnumeration.ComputableIsomorphism
