-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableWords.freeGroup_primrec_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:46:01.124623+00:00
-- url     : https://prove2.me/submissions/aa35dbd5-0c0e-46d3-9036-fa02dc65ac4a

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Computability_ComputableWords

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableWords
variable {α : Type*} [Primcodable α] [DecidableEq α]
namespace Kourovka.MetabelianEnumeration.ComputableWords
theorem _root_.solution {β : Type*} [Primcodable β] {f : β → FreeGroup α} :
    Primrec f ↔ Primrec (fun b => (f b).toWord) := by
  rw [← Primrec.of_equiv_iff reducedWordEquiv, ← Primrec.subtype_val_iff]
  rfl
end Kourovka.MetabelianEnumeration.ComputableWords
