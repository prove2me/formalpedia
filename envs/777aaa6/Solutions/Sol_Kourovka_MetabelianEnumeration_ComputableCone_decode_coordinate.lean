-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCone.decode_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:52:36.699748+00:00
-- url     : https://prove2.me/submissions/6cad9b47-ea83-40e4-9627-cfaf620387d9

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
namespace Kourovka.MetabelianEnumeration.ComputableCone
theorem _root_.solution (n : ℕ) (i : Fin n) (a b : ℤ) :
    decodeRow n (coordinate n i a b) = ConeVerifier.coordinate i (a : ℚ) (b : ℚ) := by
  apply congrArg₂ (FourierMotzkin.Row.mk (n := n))
  · ext j
    simp [coordinate, ComputableFourierMotzkin.coeff,
      List.getD_eq_getElem?_getD, j.isLt, Fin.ext_iff]
  · rfl
end Kourovka.MetabelianEnumeration.ComputableCone
