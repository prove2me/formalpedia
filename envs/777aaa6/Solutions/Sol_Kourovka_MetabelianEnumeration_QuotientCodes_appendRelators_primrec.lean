-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.QuotientCodes.appendRelators_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:08:50.332175+00:00
-- url     : https://prove2.me/submissions/694a048f-c01f-4145-8ee2-89d8384dc4dd

import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Definitions.Def_Kourovka_Presentations_FiniteQuotient
import Definitions.Def_Kourovka_Presentations_QuotientCodes

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.QuotientCodes
open NaturalWordSubstitution WordCertificates
namespace Kourovka.MetabelianEnumeration.QuotientCodes
theorem _root_.solution : Primrec₂ appendRelators :=
  (Primrec.fst.comp Primrec.fst).pair
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
end Kourovka.MetabelianEnumeration.QuotientCodes
