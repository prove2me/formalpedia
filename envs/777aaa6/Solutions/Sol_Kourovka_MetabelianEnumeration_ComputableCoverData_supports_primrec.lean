-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverData.supports_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:07:44.73343+00:00
-- url     : https://prove2.me/submissions/5ce5b6e4-3695-4adf-b24e-274966c1cf50

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover
namespace Kourovka.MetabelianEnumeration.ComputableCoverData
theorem _root_.solution : Primrec supports :=
  Primrec.list_map (Primrec.snd.comp Primrec.snd)
    (Primrec.list_map (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd).to₂).to₂
end Kourovka.MetabelianEnumeration.ComputableCoverData
