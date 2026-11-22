-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIntegers.abs_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:17:32.374513+00:00
-- url     : https://prove2.me/submissions/c7a6c4e2-a27b-4290-a1a1-a6371532264b

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_ofNat_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_natAbs_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableIntegers
theorem _root_.solution : Primrec (fun z : ℤ => |z|) :=
  (ofNat_primrec.comp natAbs_primrec).of_eq (fun z => Int.natCast_natAbs z)
end Kourovka.MetabelianEnumeration.ComputableIntegers
