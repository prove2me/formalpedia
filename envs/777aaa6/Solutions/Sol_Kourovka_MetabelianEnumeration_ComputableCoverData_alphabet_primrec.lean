-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverData.alphabet_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:48:00.889452+00:00
-- url     : https://prove2.me/submissions/9de30845-02b1-46f2-83bd-affd7ba39841

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover
namespace Kourovka.MetabelianEnumeration.ComputableCoverData
theorem _root_.solution : Primrec alphabet :=
  Primrec.succ.comp (Primrec.snd.comp Primrec.fst)
end Kourovka.MetabelianEnumeration.ComputableCoverData
