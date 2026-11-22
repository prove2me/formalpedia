-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverWords.of_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:49:34.042085+00:00
-- url     : https://prove2.me/submissions/14185fbe-1480-49cd-8dba-8a2500e56f65

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_mk_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData
namespace Kourovka.MetabelianEnumeration.ComputableCoverWords
theorem _root_.solution : Primrec (FreeGroup.of : ℕ → WordGroup) :=
  ComputableWords.mk_primrec.comp (Primrec.list_cons.comp
    (Primrec.id.pair (Primrec.const true)) (Primrec.const []))
end Kourovka.MetabelianEnumeration.ComputableCoverWords
