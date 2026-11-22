-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCone.prependChoices_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:06:59.090902+00:00
-- url     : https://prove2.me/submissions/62280e64-b38b-420c-8180-faa4720ebfcd

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_supportRow_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
namespace Kourovka.MetabelianEnumeration.ComputableCone
theorem _root_.solution : Primrec₂ prependChoices :=
  Primrec.list_flatMap (Primrec.snd.comp Primrec.fst)
    (Primrec.list_map (Primrec.snd.comp Primrec.fst)
      (Primrec.list_cons.comp
        (supportRow_primrec.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂).to₂
end Kourovka.MetabelianEnumeration.ComputableCone
