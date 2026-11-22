-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceModule.shift_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:58:39.413193+00:00
-- url     : https://prove2.me/submissions/3378fc30-6f85-4621-af3d-011d66523f7c

import Definitions.Def_Kourovka_Modules_ValuationModule
import Definitions.Def_Kourovka_Halfspaces_HalfspaceModule

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceModule
open ValuationModule
variable {Q M : Type} [AddCommGroup Q] [DecidableEq Q]
variable [AddCommGroup M] [Module (GroupRing Q) M]
namespace Kourovka.MetabelianEnumeration.HalfspaceModule
theorem _root_.solution (χ : Q →+ ℝ) (V : Submodule (nonnegativeRing χ) M)
    (q : Q) (hq : 0 ≤ χ q) (m : M) (hm : m ∈ V) : shift q m ∈ V :=
  V.smul_mem (halfMonomial χ q hq) hm
end Kourovka.MetabelianEnumeration.HalfspaceModule
