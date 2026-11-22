-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceModule.monomial_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:58:38.92561+00:00
-- url     : https://prove2.me/submissions/5997a549-409c-43e3-81cc-74a4a6b98178

import Definitions.Def_Kourovka_Modules_ValuationModule
import Definitions.Def_Kourovka_Halfspaces_HalfspaceModule

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceModule
open ValuationModule
variable {Q M : Type} [AddCommGroup Q] [DecidableEq Q]
variable [AddCommGroup M] [Module (GroupRing Q) M]
omit [DecidableEq Q]
namespace Kourovka.MetabelianEnumeration.HalfspaceModule
theorem _root_.solution (q r : Q) : monomial (q + r) = monomial q * monomial r := by
  simp [monomial, AddMonoidAlgebra.single_mul_single]
end Kourovka.MetabelianEnumeration.HalfspaceModule
