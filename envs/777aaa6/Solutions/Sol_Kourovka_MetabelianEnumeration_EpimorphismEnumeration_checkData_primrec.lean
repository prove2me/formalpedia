-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.EpimorphismEnumeration.checkData_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:28:34.816249+00:00
-- url     : https://prove2.me/submissions/7944b618-9423-449f-9afe-6568be9a8d15

import Definitions.Def_Kourovka_Certificates_EpimorphismSemantics
import Definitions.Def_Kourovka_Enumeration_EnumerationCofinality
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
import Definitions.Def_Kourovka_Enumeration_EpimorphismEnumeration
import Theorems.Thm_Kourovka_MetabelianEnumeration_EpimorphismEnumeration_source_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_check_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_check_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_check_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_source_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEpimorphism_checkEpi_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_check_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_wellFormed_primrec


set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.EpimorphismEnumeration
namespace Kourovka.MetabelianEnumeration.EpimorphismEnumeration
theorem _root_.solution : Primrec₂ checkData := by
  let dataProjection : Primrec (fun z : PresentationCode × Certificate => z.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  let marginProjection : Primrec (fun z : PresentationCode × Certificate => z.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  exact Primrec.and.comp (ComputablePresentations.wellFormed_primrec.decide.comp Primrec.fst)
    (Primrec.or.comp
      ((Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 0)).decide)
      (Primrec.and.comp (ComputableCoverData.check_primrec.comp dataProjection marginProjection)
        (ComputableEpimorphism.checkEpi_primrec.comp
          ((source_primrec.comp Primrec.snd).pair Primrec.fst)
          (Primrec.snd.comp Primrec.snd))))
end Kourovka.MetabelianEnumeration.EpimorphismEnumeration
