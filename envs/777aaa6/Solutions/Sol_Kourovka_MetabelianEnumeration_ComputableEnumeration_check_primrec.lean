-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableEnumeration.check_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:24:09.381946+00:00
-- url     : https://prove2.me/submissions/47a69e2a-3e30-47e6-bb74-dfb750c63276

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Presentations_QuotientCodes
import Definitions.Def_Kourovka_Enumeration_ComputableEnumeration
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_checkData_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_decodeCertificate_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_checkData_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_decodePresentation_primrec


set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEnumeration
namespace Kourovka.MetabelianEnumeration.ComputableEnumeration
theorem _root_.solution : Primrec₂ check :=
  checkData_primrec.comp (ComputablePresentations.decodePresentation_primrec.comp Primrec.fst)
    (decodeCertificate_primrec.comp Primrec.snd)
end Kourovka.MetabelianEnumeration.ComputableEnumeration
