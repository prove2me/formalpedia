-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCone.powTwo_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:02:28.587297+00:00
-- url     : https://prove2.me/submissions/0bb27f58-9bdf-4209-8f4c-5811b1f155e9

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_nat_pow_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_ofNat_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
namespace Kourovka.MetabelianEnumeration.ComputableCone
theorem _root_.solution : Primrec (fun r : ℕ => (2 ^ r : ℤ)) :=
  (ofNat_primrec.comp (nat_pow_primrec.comp (Primrec.const 2) Primrec.id)).of_eq (fun r => by simp)
end Kourovka.MetabelianEnumeration.ComputableCone
