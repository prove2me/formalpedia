-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableEnumeration.decodeDefault_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:56:33.465758+00:00
-- url     : https://prove2.me/submissions/abc9a884-00f5-41ef-9dcb-40a4e2090dea

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Presentations_QuotientCodes
import Definitions.Def_Kourovka_Enumeration_ComputableEnumeration

set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEnumeration
namespace Kourovka.MetabelianEnumeration.ComputableEnumeration
theorem _root_.solution {α : Type} [Primcodable α] (fallback : α) :
    Primrec (fun n : ℕ => (Encodable.decode (α := α) n).getD fallback) :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const fallback)
end Kourovka.MetabelianEnumeration.ComputableEnumeration
