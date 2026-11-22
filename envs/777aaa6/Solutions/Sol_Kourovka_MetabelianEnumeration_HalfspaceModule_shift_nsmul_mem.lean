-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceModule.shift_nsmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:59:26.806112+00:00
-- url     : https://prove2.me/submissions/2054851e-5b22-4fd9-b405-3d7b9c7e20bd

import Definitions.Def_Kourovka_Modules_ValuationModule
import Definitions.Def_Kourovka_Halfspaces_HalfspaceModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceModule_shift_mem

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceModule
open ValuationModule
variable {Q M : Type} [AddCommGroup Q] [DecidableEq Q]
variable [AddCommGroup M] [Module (GroupRing Q) M]
namespace Kourovka.MetabelianEnumeration.HalfspaceModule
theorem _root_.solution (χ : Q →+ ℝ) (V : Submodule (nonnegativeRing χ) M)
    (u : Q) (hu : 0 ≤ χ u) (n : ℕ) (m : M) (hm : m ∈ V) : shift (n • u) m ∈ V := by
  apply shift_mem χ V _ _ m hm
  simpa only [map_nsmul, nsmul_eq_mul] using mul_nonneg (Nat.cast_nonneg n) hu
end Kourovka.MetabelianEnumeration.HalfspaceModule
