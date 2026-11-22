-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.coeff_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:52:01.515403+00:00
-- url     : https://prove2.me/submissions/533bfaea-2d53-4ce3-8f9d-66131ea70b9f

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
theorem _root_.solution : Primrec₂ coeff :=
  (Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd
end Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
