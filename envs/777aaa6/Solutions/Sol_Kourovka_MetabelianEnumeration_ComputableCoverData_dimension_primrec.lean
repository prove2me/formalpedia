-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverData.dimension_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:48:00.432577+00:00
-- url     : https://prove2.me/submissions/3dc6ee79-41d6-4d9f-bc1e-21d1bd68ed5b

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover
namespace Kourovka.MetabelianEnumeration.ComputableCoverData
theorem _root_.solution : Primrec dimension :=
  Primrec.succ.comp (Primrec.fst.comp Primrec.fst)
end Kourovka.MetabelianEnumeration.ComputableCoverData
