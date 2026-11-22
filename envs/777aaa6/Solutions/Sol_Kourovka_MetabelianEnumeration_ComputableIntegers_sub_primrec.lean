-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIntegers.sub_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:04:12.395442+00:00
-- url     : https://prove2.me/submissions/5b078bb8-233a-4be9-b988-0613eec42139

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_neg_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_add_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableIntegers
theorem _root_.solution : Primrec₂ (fun x y : ℤ => x - y) :=
  (add_primrec.comp Primrec.fst (neg_primrec.comp Primrec.snd)).of_eq (fun _ => rfl)
end Kourovka.MetabelianEnumeration.ComputableIntegers
