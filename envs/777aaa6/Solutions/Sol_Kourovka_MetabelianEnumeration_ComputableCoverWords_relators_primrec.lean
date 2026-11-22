-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverWords.relators_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:18:03.786197+00:00
-- url     : https://prove2.me/submissions/32dd5dff-0c54-4eed-973b-61475af18103

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_tRelators_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_shortRelators_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_polynomialRelators_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData
namespace Kourovka.MetabelianEnumeration.ComputableCoverWords
theorem _root_.solution : Primrec₂ relators :=
  Primrec.list_append.comp
    (Primrec.list_append.comp (tRelators_primrec.comp Primrec.fst) shortRelators_primrec)
    (polynomialRelators_primrec.comp Primrec.fst)
end Kourovka.MetabelianEnumeration.ComputableCoverWords
