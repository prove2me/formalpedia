-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIntegers.toNat_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:51:33.301243+00:00
-- url     : https://prove2.me/submissions/98a6d673-0316-46e2-b2c7-72cd10d45ad5

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_casesOn_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableIntegers
theorem _root_.solution : Primrec Int.toNat := by
  exact (casesOn_primrec Primrec.id Primrec.snd.to₂ (Primrec.const 0).to₂).of_eq
    (fun z => by cases z <;> rfl)
end Kourovka.MetabelianEnumeration.ComputableIntegers
