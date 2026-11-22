-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIntegers.negSucc_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:00:50.478988+00:00
-- url     : https://prove2.me/submissions/b030f847-71f8-4054-adb8-cf1b6f9fce52

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableIntegers
theorem _root_.solution : Primrec Int.negSucc :=
  (Primrec.of_equiv_symm (e := Equiv.intEquivNatSumNat)).comp Primrec.sumInr
end Kourovka.MetabelianEnumeration.ComputableIntegers
