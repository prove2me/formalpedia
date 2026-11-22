-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.EpimorphismEnumeration.source_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:26:54.387577+00:00
-- url     : https://prove2.me/submissions/3f234525-130c-4667-9f48-3d5af6dd840a

import Definitions.Def_Kourovka_Certificates_EpimorphismSemantics
import Definitions.Def_Kourovka_Enumeration_EnumerationCofinality
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
import Definitions.Def_Kourovka_Enumeration_EpimorphismEnumeration
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_radius_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_presentation_primrec


set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.EpimorphismEnumeration
namespace Kourovka.MetabelianEnumeration.EpimorphismEnumeration
theorem _root_.solution : Primrec source :=
  ComputableCoverWords.presentation_primrec.comp (Primrec.fst.comp Primrec.fst)
    (ComputableCoverData.radius_primrec.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst))
end Kourovka.MetabelianEnumeration.EpimorphismEnumeration
