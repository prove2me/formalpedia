-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableEnumeration.source_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:20:19.677706+00:00
-- url     : https://prove2.me/submissions/c02cdc6d-9291-4e28-9f2f-ddc94e81a1b6

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Presentations_QuotientCodes
import Definitions.Def_Kourovka_Enumeration_ComputableEnumeration
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_radius_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_presentation_primrec


set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEnumeration
namespace Kourovka.MetabelianEnumeration.ComputableEnumeration
theorem _root_.solution : Primrec source :=
  ComputableCoverWords.presentation_primrec.comp (Primrec.fst.comp Primrec.fst)
    (ComputableCoverData.radius_primrec.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst))
end Kourovka.MetabelianEnumeration.ComputableEnumeration
