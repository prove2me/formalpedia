-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceModule.shift_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:59:38.249144+00:00
-- url     : https://prove2.me/submissions/7b9b2472-25c0-44f4-bffd-d0ab432948ec

import Definitions.Def_Kourovka_Modules_ValuationModule
import Definitions.Def_Kourovka_Halfspaces_HalfspaceModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceModule_monomial_add

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceModule
open ValuationModule
variable {Q M : Type} [AddCommGroup Q] [DecidableEq Q]
variable [AddCommGroup M] [Module (GroupRing Q) M]
omit [DecidableEq Q]
namespace Kourovka.MetabelianEnumeration.HalfspaceModule
theorem _root_.solution (q r : Q) (m : M) : shift q (shift r m) = shift (q + r) m := by
  simp only [shift, monomial_add, mul_smul]
end Kourovka.MetabelianEnumeration.HalfspaceModule
