-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceModule.shift_difference_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:15:03.475914+00:00
-- url     : https://prove2.me/submissions/622fec5a-d9d7-4539-a232-11f812606020

import Definitions.Def_Kourovka_Modules_ValuationModule
import Definitions.Def_Kourovka_Halfspaces_HalfspaceModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceModule_shift_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceModule_shift_nsmul_mem

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceModule
open ValuationModule
variable {Q M : Type} [AddCommGroup Q] [DecidableEq Q]
variable [AddCommGroup M] [Module (GroupRing Q) M]
namespace Kourovka.MetabelianEnumeration.HalfspaceModule
theorem _root_.solution (χ : Q →+ ℝ) (u : Q) (hu : 0 ≤ χ u)
    (V : Submodule (nonnegativeRing χ) M) (m : M)
    (hm : shift u m - m ∈ V) (n : ℕ) : shift (n • u) m - m ∈ V := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := V.add_mem (shift_nsmul_mem χ V u hu n _ hm) ih
    have heq : shift (n • u) (shift u m - m) + (shift (n • u) m - m) =
        shift ((n + 1) • u) m - m := by
      rw [shift_sub, shift_shift, add_nsmul, one_nsmul]
      abel
    exact heq ▸ h
end Kourovka.MetabelianEnumeration.HalfspaceModule
