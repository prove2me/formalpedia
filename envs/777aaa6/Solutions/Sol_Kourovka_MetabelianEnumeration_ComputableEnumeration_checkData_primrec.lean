-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableEnumeration.checkData_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:23:13.377145+00:00
-- url     : https://prove2.me/submissions/263f9d19-776c-44c4-9ccd-c2f492e3d78f

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Presentations_QuotientCodes
import Definitions.Def_Kourovka_Enumeration_ComputableEnumeration
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_extended_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_check_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_check_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_check_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_checkIso_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_wellFormed_primrec


set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEnumeration
namespace Kourovka.MetabelianEnumeration.ComputableEnumeration
theorem _root_.solution : Primrec₂ checkData := by
  let hd : Primrec (fun z : PresentationCode × Certificate => z.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  let hr : Primrec (fun z : PresentationCode × Certificate => z.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  let hi : Primrec (fun z : PresentationCode × Certificate => z.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.and.comp (ComputablePresentations.wellFormed_primrec.decide.comp Primrec.fst)
    (Primrec.or.comp
      ((Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 0)).decide)
      (Primrec.and.comp (ComputableCoverData.check_primrec.comp hd hr)
        (ComputableIsomorphism.checkIso_primrec.comp
          ((extended_primrec.comp Primrec.snd).pair Primrec.fst) hi)))
end Kourovka.MetabelianEnumeration.ComputableEnumeration
