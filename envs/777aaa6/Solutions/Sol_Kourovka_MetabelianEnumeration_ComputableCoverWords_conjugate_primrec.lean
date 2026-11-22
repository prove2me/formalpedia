-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverWords.conjugate_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:05:54.089185+00:00
-- url     : https://prove2.me/submissions/910cae88-712c-4d6a-aa14-f8a9d01e435d

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
theorem _root_.solution : Primrec₂ (FiniteCover.conjugate : WordGroup → WordGroup → WordGroup) :=
  ComputableWords.mul_primrec.comp
    (ComputableWords.mul_primrec.comp (ComputableWords.inv_primrec.comp Primrec.snd) Primrec.fst)
    Primrec.snd
end Kourovka.MetabelianEnumeration.ComputableCoverWords
