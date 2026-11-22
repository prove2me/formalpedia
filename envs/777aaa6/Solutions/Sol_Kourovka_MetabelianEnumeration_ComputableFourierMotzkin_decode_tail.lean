-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.decode_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:01:54.960071+00:00
-- url     : https://prove2.me/submissions/2133861d-17bf-4c56-a4f9-0cfc6f03fb1c

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
theorem _root_.solution (n : ℕ) (r : RowCode) :
    decodeRow n (tail r) = (decodeRow (n + 1) r).tail := by
  apply congrArg₂ (FourierMotzkin.Row.mk (n := n))
  · ext i
    simp [decodeRow, tail, coeff, List.getD_eq_getElem?_getD]
  · rfl
end Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
