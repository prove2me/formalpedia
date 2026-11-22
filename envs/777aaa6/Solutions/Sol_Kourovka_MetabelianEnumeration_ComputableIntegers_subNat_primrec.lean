-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIntegers.subNat_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:01:39.919839+00:00
-- url     : https://prove2.me/submissions/6dc6aca9-839d-45c1-bcdb-a49e676fbbc2

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_ofNat_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_negSucc_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableIntegers
theorem _root_.solution : Primrec₂ subNat :=
  Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
    (ofNat_primrec.comp Primrec.nat_sub)
    (negSucc_primrec.comp (Primrec.nat_sub.comp
      (Primrec.nat_sub.comp Primrec.snd Primrec.fst) (Primrec.const 1)))
end Kourovka.MetabelianEnumeration.ComputableIntegers
