-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverWords.tRelator_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:10:13.591673+00:00
-- url     : https://prove2.me/submissions/4392c480-289e-4bd7-b3d5-7b9a506c7212

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_of_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_rightComm_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_designated_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_dimension_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_mul_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_inv_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_mul_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData
namespace Kourovka.MetabelianEnumeration.ComputableCoverWords
theorem _root_.solution : Primrec tRelator :=
  ComputableWords.mul_primrec.comp
    (rightComm_primrec.comp (of_primrec.comp (Primrec.fst.comp Primrec.snd))
      (of_primrec.comp (Primrec.snd.comp Primrec.snd)))
    (ComputableWords.inv_primrec.comp (of_primrec.comp
      (Primrec.nat_add.comp (dimension_primrec.comp Primrec.fst) designated_primrec)))
end Kourovka.MetabelianEnumeration.ComputableCoverWords
