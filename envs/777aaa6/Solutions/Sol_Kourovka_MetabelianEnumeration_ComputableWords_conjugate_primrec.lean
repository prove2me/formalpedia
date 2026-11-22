-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableWords.conjugate_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:52:15.891179+00:00
-- url     : https://prove2.me/submissions/b2b01318-53e6-438c-b7fd-7be162960419

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Computability_ComputableWords
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_mul_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_inv_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableWords
variable {α : Type*} [Primcodable α] [DecidableEq α]
namespace Kourovka.MetabelianEnumeration.ComputableWords
theorem _root_.solution : Primrec₂ (fun g x : FreeGroup α => g * x * g⁻¹) :=
  mul_primrec.comp (mul_primrec.comp Primrec.fst Primrec.snd)
    (inv_primrec.comp Primrec.fst)
end Kourovka.MetabelianEnumeration.ComputableWords
