-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputablePresentations.naturalRelators_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:00:06.213949+00:00
-- url     : https://prove2.me/submissions/7f298614-6a9b-40bc-afdc-0026600633cc

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_mk_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords
namespace Kourovka.MetabelianEnumeration.ComputablePresentations
theorem _root_.solution : Primrec naturalRelators :=
  Primrec.list_map Primrec.snd (mk_primrec.comp Primrec.snd).to₂
end Kourovka.MetabelianEnumeration.ComputablePresentations
