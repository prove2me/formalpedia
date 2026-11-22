-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.combine_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:06:56.872518+00:00
-- url     : https://prove2.me/submissions/c3e70ebb-e36d-4d08-b82c-ba236a18b679

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_head_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_combineCoeff_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_mul_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_sub_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_mul_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
theorem _root_.solution : Primrec combine :=
  (Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_max.comp
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))))
    (combineCoeff_primrec.comp Primrec.fst (Primrec.succ.comp Primrec.snd)).to₂).pair
    (sub_primrec.comp
      (mul_primrec.comp (head_primrec.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
      (mul_primrec.comp (head_primrec.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)))
end Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
