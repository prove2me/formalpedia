-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIntegers.neg_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:02:38.127044+00:00
-- url     : https://prove2.me/submissions/2c32f018-63d8-4a25-88e9-21fc5a62ec4b

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_ofNat_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_casesOn_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_subNat_eq
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_subNat_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableIntegers
theorem _root_.solution : Primrec (fun z : ℤ => -z) := by
  apply (casesOn_primrec Primrec.id
    (subNat_primrec.comp (Primrec.const 0) Primrec.snd).to₂
    (ofNat_primrec.comp (Primrec.succ.comp Primrec.snd)).to₂).of_eq
  intro z
  cases z with
  | ofNat n => change subNat 0 n = -(n : ℤ); simp [subNat_eq]
  | negSucc n => rfl
end Kourovka.MetabelianEnumeration.ComputableIntegers
