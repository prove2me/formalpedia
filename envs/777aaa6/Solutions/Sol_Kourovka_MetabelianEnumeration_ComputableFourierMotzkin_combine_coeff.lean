-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.combine_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:01:55.549648+00:00
-- url     : https://prove2.me/submissions/9e3e8ce8-3a03-4015-a00f-4029c4366078

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
theorem _root_.solution (p : RowCode × RowCode) (i : ℕ) :
    coeff (combine p) i = combineCoeff p (i + 1) := by
  by_cases hi : i < max p.1.1.length p.2.1.length
  · simp [coeff, combine, List.getD_eq_getElem?_getD, hi]
  · have hleft : p.1.1.length ≤ i + 1 := by omega
    have hright : p.2.1.length ≤ i + 1 := by omega
    simp [coeff, combine, combineCoeff, List.getD_eq_getElem?_getD, hi,
      List.getElem?_eq_none hleft, List.getElem?_eq_none hright]
end Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
