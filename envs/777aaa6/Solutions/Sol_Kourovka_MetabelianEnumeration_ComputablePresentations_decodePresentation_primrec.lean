-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputablePresentations.decodePresentation_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:50:53.234471+00:00
-- url     : https://prove2.me/submissions/a49614da-e096-41e8-a5ba-18bbd61024dd

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords
namespace Kourovka.MetabelianEnumeration.ComputablePresentations
theorem _root_.solution : Primrec decodePresentation :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const (0, []))
end Kourovka.MetabelianEnumeration.ComputablePresentations
