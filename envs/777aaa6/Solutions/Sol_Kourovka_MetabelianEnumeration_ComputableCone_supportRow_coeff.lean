-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCone.supportRow_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:02:06.548804+00:00
-- url     : https://prove2.me/submissions/bc8fa1a5-7dbc-4c40-8651-22a5d8d52346

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
namespace Kourovka.MetabelianEnumeration.ComputableCone
theorem _root_.solution (n r : ℕ) (v : VectorCode) (i : Fin n) :
    (decodeRow n (supportRow r v)).coeff i = (2 ^ r : ℚ) * decodeVector n v i := by
  change (((v.map fun z => (2 ^ r : ℤ) * z).getD i 0 : ℤ) : ℚ) = _
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hv : v[(i : ℕ)]? <;> simp [hv, decodeVector, List.getD_eq_getElem?_getD]
end Kourovka.MetabelianEnumeration.ComputableCone
