-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverWords.rightComm_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:05:53.555647+00:00
-- url     : https://prove2.me/submissions/579f35d9-2fbb-4d3b-9f49-5782b310c121

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_mul_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_inv_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_mul_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData
namespace Kourovka.MetabelianEnumeration.ComputableCoverWords
theorem _root_.solution : Primrec₂ (FiniteCover.rightComm : WordGroup → WordGroup → WordGroup) :=
  ComputableWords.mul_primrec.comp
    (ComputableWords.mul_primrec.comp
      (ComputableWords.mul_primrec.comp (ComputableWords.inv_primrec.comp Primrec.fst)
        (ComputableWords.inv_primrec.comp Primrec.snd)) Primrec.fst) Primrec.snd
end Kourovka.MetabelianEnumeration.ComputableCoverWords
