-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputablePresentations.checkTrivial_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:03:40.668416+00:00
-- url     : https://prove2.me/submissions/6b5483e7-a51c-4047-bc67-f4c311e269c1

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_naturalRelators_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_validInput_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_checkNat_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_inv_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_mk_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_mul_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords
namespace Kourovka.MetabelianEnumeration.ComputablePresentations
theorem _root_.solution : Primrec₂ checkTrivial :=
  Primrec.and.comp (validInput_primrec.decide.comp Primrec.fst)
    ((ComputableClosure.checkNat_primrec mul_primrec inv_primrec).comp
      (((naturalRelators_primrec.comp Primrec.fst).pair (mk_primrec.comp Primrec.snd)).comp
        Primrec.fst) Primrec.snd)
end Kourovka.MetabelianEnumeration.ComputablePresentations
