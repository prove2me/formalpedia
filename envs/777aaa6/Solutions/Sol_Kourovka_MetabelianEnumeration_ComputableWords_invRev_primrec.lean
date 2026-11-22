-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableWords.invRev_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:50:38.488002+00:00
-- url     : https://prove2.me/submissions/a34f79ef-97ee-403a-b87a-26df329bf046

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Computability_ComputableWords

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableWords
variable {α : Type*} [Primcodable α] [DecidableEq α]
omit [DecidableEq α]
namespace Kourovka.MetabelianEnumeration.ComputableWords
theorem _root_.solution : Primrec (@FreeGroup.invRev α) :=
  Primrec.list_reverse.comp <|
    Primrec.list_map Primrec.id
      ((Primrec.fst.comp Primrec.snd).pair
        (Primrec.not.comp (Primrec.snd.comp Primrec.snd))).to₂
end Kourovka.MetabelianEnumeration.ComputableWords
