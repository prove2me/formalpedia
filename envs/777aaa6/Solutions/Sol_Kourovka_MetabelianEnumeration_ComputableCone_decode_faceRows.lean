-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCone.decode_faceRows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:03:11.466091+00:00
-- url     : https://prove2.me/submissions/9dc629c5-99ce-4163-b37e-e674e8949241

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_decode_coordinate
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_decode_cubeRows

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
namespace Kourovka.MetabelianEnumeration.ComputableCone
theorem _root_.solution (n : ℕ) (i : Fin n) (sign : ℤ) :
    (faceRows n i sign).map (decodeRow n) = ConeVerifier.faceRows i (sign : ℚ) := by
  simp only [faceRows, List.map_append, List.map_cons, List.map_nil, decode_coordinate,
    decode_cubeRows, Int.cast_one, Int.cast_neg, ConeVerifier.faceRows]
end Kourovka.MetabelianEnumeration.ComputableCone
