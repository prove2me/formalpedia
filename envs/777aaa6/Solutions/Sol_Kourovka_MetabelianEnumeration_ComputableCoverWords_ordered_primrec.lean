-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverWords.ordered_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:11:38.029174+00:00
-- url     : https://prove2.me/submissions/10ea8842-9ac7-4cda-b2c9-024ac606b65a

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_of_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_zpow_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_prod_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData
namespace Kourovka.MetabelianEnumeration.ComputableCoverWords
theorem _root_.solution : Primrec₂ ordered :=
  prod_primrec.comp (Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (zpow_primrec.comp (of_primrec.comp Primrec.snd)
      ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂)
end Kourovka.MetabelianEnumeration.ComputableCoverWords
