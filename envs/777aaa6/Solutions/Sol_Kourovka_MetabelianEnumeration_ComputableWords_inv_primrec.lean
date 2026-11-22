-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableWords.inv_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:51:24.694707+00:00
-- url     : https://prove2.me/submissions/aee83dff-ae50-4b43-a180-bfba7d5761da

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Computability_ComputableWords
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_toWord_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_freeGroup_primrec_iff
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_invRev_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableWords
variable {α : Type*} [Primcodable α] [DecidableEq α]
namespace Kourovka.MetabelianEnumeration.ComputableWords
theorem _root_.solution : Primrec (fun x : FreeGroup α => x⁻¹) :=
  freeGroup_primrec_iff.mpr <|
    (invRev_primrec.comp toWord_primrec).of_eq (fun g => (FreeGroup.toWord_inv g).symm)
end Kourovka.MetabelianEnumeration.ComputableWords
