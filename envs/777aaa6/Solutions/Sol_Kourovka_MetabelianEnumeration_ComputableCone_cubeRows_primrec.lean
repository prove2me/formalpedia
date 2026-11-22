-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCone.cubeRows_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:02:31.53552+00:00
-- url     : https://prove2.me/submissions/28247e96-9ff4-4ab1-b899-0c99e179d8e0

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_coordinate_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
namespace Kourovka.MetabelianEnumeration.ComputableCone
theorem _root_.solution : Primrec cubeRows :=
  Primrec.list_flatMap Primrec.list_range
    (Primrec.list_cons.comp (coordinate_primrec.comp
      (Primrec.id.pair ((Primrec.const 1).pair (Primrec.const (-1)))))
      (Primrec.list_cons.comp (coordinate_primrec.comp
        (Primrec.id.pair ((Primrec.const (-1)).pair (Primrec.const (-1)))))
        (Primrec.const []))).to₂
end Kourovka.MetabelianEnumeration.ComputableCone
