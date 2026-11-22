-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIntegers.natAbs_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:46:21.067817+00:00
-- url     : https://prove2.me/submissions/3bf85bae-c3e2-4cc2-b333-5875ff706a26

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_casesOn_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableIntegers
theorem _root_.solution : Primrec Int.natAbs := by
  exact (casesOn_primrec Primrec.id Primrec.snd.to₂ (Primrec.succ.comp Primrec.snd).to₂).of_eq
    (fun z => by cases z <;> rfl)
end Kourovka.MetabelianEnumeration.ComputableIntegers
