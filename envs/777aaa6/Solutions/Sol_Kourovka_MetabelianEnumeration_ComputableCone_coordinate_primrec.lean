-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCone.coordinate_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:53:05.232291+00:00
-- url     : https://prove2.me/submissions/63be0355-36af-4329-b55c-96f32167d112

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
namespace Kourovka.MetabelianEnumeration.ComputableCone
theorem _root_.solution : Primrec (fun p : (ℕ × ℕ) × (ℤ × ℤ) =>
    coordinate p.1.1 p.1.2 p.2.1 p.2.2) :=
  (Primrec.list_map (Primrec.list_range.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const 0)).to₂).pair
    (Primrec.snd.comp Primrec.snd)
end Kourovka.MetabelianEnumeration.ComputableCone
