-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableEnumeration.extended_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:21:38.64368+00:00
-- url     : https://prove2.me/submissions/c5c3a1ae-4b0b-4492-a1ec-20d0c10d2654

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Presentations_QuotientCodes
import Definitions.Def_Kourovka_Enumeration_ComputableEnumeration
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_source_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_QuotientCodes_appendRelators_primrec


set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEnumeration
namespace Kourovka.MetabelianEnumeration.ComputableEnumeration
theorem _root_.solution : Primrec extended :=
  QuotientCodes.appendRelators_primrec.comp source_primrec (Primrec.fst.comp Primrec.snd)
end Kourovka.MetabelianEnumeration.ComputableEnumeration
