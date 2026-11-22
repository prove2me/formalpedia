-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceModule.monomial_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:13:57.094287+00:00
-- url     : https://prove2.me/submissions/b693f0d1-b07c-4cd3-9659-cd2e9717f403

import Definitions.Def_Kourovka_Modules_ValuationModule
import Definitions.Def_Kourovka_Halfspaces_HalfspaceModule

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceModule
open ValuationModule
variable {Q M : Type} [AddCommGroup Q] [DecidableEq Q]
variable [AddCommGroup M] [Module (GroupRing Q) M]
namespace Kourovka.MetabelianEnumeration.HalfspaceModule
theorem _root_.solution (χ : Q →+ ℝ) (q : Q) :
    LowerBound χ (monomial q) (χ q) := by
  intro u hu
  have : u = q := by
    simpa [monomial, AddMonoidAlgebra.single_apply, eq_comm] using hu
  simp [this]
end Kourovka.MetabelianEnumeration.HalfspaceModule
