-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableWords.mk_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:46:48.376306+00:00
-- url     : https://prove2.me/submissions/f6f5ea94-ae2e-4531-bb14-3b14115b9253

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Computability_ComputableWords
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_freeGroup_primrec_iff

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableWords
variable {α : Type*} [Primcodable α] [DecidableEq α]
namespace Kourovka.MetabelianEnumeration.ComputableWords
theorem _root_.solution : Primrec (@FreeGroup.mk α) :=
  freeGroup_primrec_iff.mpr reduce_primrec
end Kourovka.MetabelianEnumeration.ComputableWords
