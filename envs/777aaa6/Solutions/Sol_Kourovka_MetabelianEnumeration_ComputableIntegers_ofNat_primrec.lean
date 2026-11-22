-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIntegers.ofNat_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:43:43.146287+00:00
-- url     : https://prove2.me/submissions/9de9286e-883a-47cb-a5d4-545e7f2e0096

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableIntegers
theorem _root_.solution : Primrec (fun n : ℕ => (n : ℤ)) :=
  (Primrec.of_equiv_symm (e := Equiv.intEquivNatSumNat)).comp Primrec.sumInl
end Kourovka.MetabelianEnumeration.ComputableIntegers
