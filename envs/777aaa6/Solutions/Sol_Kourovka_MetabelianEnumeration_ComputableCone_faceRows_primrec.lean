-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCone.faceRows_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:03:31.633197+00:00
-- url     : https://prove2.me/submissions/94a7b9b9-68a4-4b16-8a6d-b2ed36635882

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_coordinate_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_cubeRows_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_neg_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
namespace Kourovka.MetabelianEnumeration.ComputableCone
theorem _root_.solution : Primrec (fun p : (ℕ × ℕ) × ℤ => faceRows p.1.1 p.1.2 p.2) :=
  Primrec.list_append.comp
    (Primrec.list_cons.comp (coordinate_primrec.comp
      (Primrec.fst.pair ((Primrec.const 1).pair (neg_primrec.comp Primrec.snd))))
      (Primrec.list_cons.comp (coordinate_primrec.comp
        (Primrec.fst.pair ((Primrec.const (-1)).pair Primrec.snd))) (Primrec.const [])))
    (cubeRows_primrec.comp (Primrec.fst.comp Primrec.fst))
end Kourovka.MetabelianEnumeration.ComputableCone
