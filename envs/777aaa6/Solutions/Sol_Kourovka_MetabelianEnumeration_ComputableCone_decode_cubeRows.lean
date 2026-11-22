-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCone.decode_cubeRows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:02:17.479468+00:00
-- url     : https://prove2.me/submissions/95dc69d8-c3d8-4c32-a625-49e4289ece9b

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_decode_coordinate

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
namespace Kourovka.MetabelianEnumeration.ComputableCone
theorem _root_.solution (n : ℕ) :
    (cubeRows n).map (decodeRow n) = ConeVerifier.cubeRows n := by
  rw [cubeRows, ← List.map_coe_finRange (n := n)]
  simp only [List.flatMap_map, List.map_flatMap, List.map_cons, List.map_nil,
    decode_coordinate, Int.cast_one, Int.cast_neg]
  rfl
end Kourovka.MetabelianEnumeration.ComputableCone
