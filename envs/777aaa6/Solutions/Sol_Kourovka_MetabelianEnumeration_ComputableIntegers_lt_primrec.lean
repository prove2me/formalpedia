-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIntegers.lt_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:04:21.2393+00:00
-- url     : https://prove2.me/submissions/e30e7a80-7bf7-4986-9ba0-f8c277d3f0be

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_le_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableIntegers
theorem _root_.solution : PrimrecRel (fun x y : ℤ => x < y) :=
  (le_primrec.comp Primrec.snd Primrec.fst).not.of_eq (fun _ => by omega)
end Kourovka.MetabelianEnumeration.ComputableIntegers
