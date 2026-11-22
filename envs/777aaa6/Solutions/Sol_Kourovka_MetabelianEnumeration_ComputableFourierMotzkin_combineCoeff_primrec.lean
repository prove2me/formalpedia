-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.combineCoeff_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:05:54.578041+00:00
-- url     : https://prove2.me/submissions/8520b271-b8cd-4461-944d-d1a0b67c628f

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_coeff_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_head_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_mul_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_sub_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_mul_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
theorem _root_.solution : Primrec₂ combineCoeff :=
  sub_primrec.comp
    (mul_primrec.comp (head_primrec.comp (Primrec.snd.comp Primrec.fst))
      (coeff_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd))
    (mul_primrec.comp (head_primrec.comp (Primrec.fst.comp Primrec.fst))
      (coeff_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
end Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
