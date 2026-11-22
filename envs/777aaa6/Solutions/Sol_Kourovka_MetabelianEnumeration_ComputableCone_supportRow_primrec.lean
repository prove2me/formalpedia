-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCone.supportRow_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:05:59.308081+00:00
-- url     : https://prove2.me/submissions/04c0ff57-f034-402f-9580-70d24ee931a6

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_powTwo_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_mul_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_mul_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
namespace Kourovka.MetabelianEnumeration.ComputableCone
theorem _root_.solution : Primrec₂ supportRow :=
  (Primrec.list_map Primrec.snd
    (mul_primrec.comp (powTwo_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂).pair
    (Primrec.const (-1))
end Kourovka.MetabelianEnumeration.ComputableCone
