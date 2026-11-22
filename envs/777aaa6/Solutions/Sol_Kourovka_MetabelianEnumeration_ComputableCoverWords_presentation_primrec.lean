-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverWords.presentation_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:19:00.602304+00:00
-- url     : https://prove2.me/submissions/ec33d13f-1797-44ae-ba4f-a486cac9e856

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_relators_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_alphabet_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_dimension_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_toWord_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData
namespace Kourovka.MetabelianEnumeration.ComputableCoverWords
theorem _root_.solution : Primrec₂ presentation :=
  (Primrec.nat_add.comp (dimension_primrec.comp Primrec.fst) (alphabet_primrec.comp Primrec.fst)).pair
    (Primrec.list_map relators_primrec (ComputableWords.toWord_primrec.comp Primrec.snd).to₂)
end Kourovka.MetabelianEnumeration.ComputableCoverWords
