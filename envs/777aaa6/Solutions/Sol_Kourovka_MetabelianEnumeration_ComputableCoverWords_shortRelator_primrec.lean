-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverWords.shortRelator_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:12:57.799877+00:00
-- url     : https://prove2.me/submissions/b1c428f4-d830-4890-b7cf-a2b511037486

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_of_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_rightComm_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_conjugate_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_ordered_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_dimension_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_conjugate_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData
namespace Kourovka.MetabelianEnumeration.ComputableCoverWords
theorem _root_.solution : Primrec shortRelator :=
  rightComm_primrec.comp
    (of_primrec.comp (Primrec.nat_add.comp (dimension_primrec.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))))
    (conjugate_primrec.comp
      (of_primrec.comp (Primrec.nat_add.comp (dimension_primrec.comp Primrec.fst)
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
      (ordered_primrec.comp (dimension_primrec.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)))
end Kourovka.MetabelianEnumeration.ComputableCoverWords
