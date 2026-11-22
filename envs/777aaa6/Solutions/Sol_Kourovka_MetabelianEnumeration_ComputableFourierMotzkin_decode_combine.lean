-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.decode_combine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:02:43.114285+00:00
-- url     : https://prove2.me/submissions/429fd7af-27ca-49a1-ba23-dcd12d1ba2f0

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_combine_coeff

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
theorem _root_.solution (n : ℕ) (p : RowCode × RowCode) :
    decodeRow n (combine p) = (decodeRow (n + 1) p.1).combine (decodeRow (n + 1) p.2) := by
  apply congrArg₂ (FourierMotzkin.Row.mk (n := n))
  · ext i
    simp [decodeRow, combine_coeff, combineCoeff,
      FourierMotzkin.Row.head, head]
  · simp [decodeRow, combine, FourierMotzkin.Row.head, head]
end Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
