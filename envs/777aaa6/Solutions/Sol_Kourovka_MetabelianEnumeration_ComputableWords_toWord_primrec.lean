-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableWords.toWord_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:46:00.205392+00:00
-- url     : https://prove2.me/submissions/32788118-4dfd-4377-9de1-fae415564578

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Computability_ComputableWords

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableWords
variable {α : Type*} [Primcodable α] [DecidableEq α]
namespace Kourovka.MetabelianEnumeration.ComputableWords
theorem _root_.solution : Primrec (@FreeGroup.toWord α _) :=
  Primrec.subtype_val.comp (Primrec.of_equiv (e := reducedWordEquiv))
end Kourovka.MetabelianEnumeration.ComputableWords
