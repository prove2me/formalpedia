-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableWords.mul_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:46:47.78681+00:00
-- url     : https://prove2.me/submissions/db3a8375-42ef-40d2-85a2-755e613e7fbb

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Computability_ComputableWords
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_toWord_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_freeGroup_primrec_iff

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableWords
variable {α : Type*} [Primcodable α] [DecidableEq α]
namespace Kourovka.MetabelianEnumeration.ComputableWords
theorem _root_.solution : Primrec₂ (fun x y : FreeGroup α => x * y) :=
  freeGroup_primrec_iff.mpr <|
    (reduce_primrec.comp (Primrec.list_append.comp
      (toWord_primrec.comp Primrec.fst) (toWord_primrec.comp Primrec.snd))).of_eq
        (fun p => (FreeGroup.toWord_mul p.1 p.2).symm)
end Kourovka.MetabelianEnumeration.ComputableWords
