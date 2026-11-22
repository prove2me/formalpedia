-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceLoops.conjugate_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:15:46.617931+00:00
-- url     : https://prove2.me/submissions/954d5a8d-cf67-4e20-b8de-deb3c8bc3a4b

import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceLoops
open HalfspaceGeometry HalfspaceModule ValuationModule
variable {E L X : Type} [Group E] [AddCommGroup L]
variable (π : E →* Multiplicative L)
variable [IsMulCommutative π.ker]
namespace Kourovka.MetabelianEnumeration.HalfspaceLoops
theorem _root_.solution (g : E) (n : Additive π.ker) :
    conjugate π g (-n) = -conjugate π g n := by
  apply Additive.toMul.injective
  exact map_inv (MulAut.conjNormal g) n.toMul
end Kourovka.MetabelianEnumeration.HalfspaceLoops
