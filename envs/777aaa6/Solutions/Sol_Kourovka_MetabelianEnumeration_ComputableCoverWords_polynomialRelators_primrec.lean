-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverWords.polynomialRelators_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:16:55.472708+00:00
-- url     : https://prove2.me/submissions/6c4e35d7-7f59-4ef9-a6e6-e74df9129d0f

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_polynomialRelator_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_alphabet_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData
namespace Kourovka.MetabelianEnumeration.ComputableCoverWords
theorem _root_.solution : Primrec polynomialRelators :=
  Primrec.list_flatMap (Primrec.list_range.comp alphabet_primrec)
    (Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) polynomialRelator_primrec.to₂).to₂
end Kourovka.MetabelianEnumeration.ComputableCoverWords
