-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableWords.wordEq_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:17:01.191145+00:00
-- url     : https://prove2.me/submissions/f31056cd-6772-4a64-ae44-4d9a290e6ef6

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Computability_ComputableWords

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableWords
variable {α : Type*} [Primcodable α] [DecidableEq α]
namespace Kourovka.MetabelianEnumeration.ComputableWords
theorem _root_.solution : Primrec₂ (@wordEq α _) :=
  Primrec.eq.decide.comp (reduce_primrec.comp Primrec.fst) (reduce_primrec.comp Primrec.snd)
end Kourovka.MetabelianEnumeration.ComputableWords
