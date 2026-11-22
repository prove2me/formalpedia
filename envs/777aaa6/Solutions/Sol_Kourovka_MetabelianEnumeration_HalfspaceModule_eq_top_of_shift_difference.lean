-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceModule.eq_top_of_shift_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:16:49.936207+00:00
-- url     : https://prove2.me/submissions/514fd742-44d9-40f3-bea3-0f83e81b76e1

import Definitions.Def_Kourovka_Modules_ValuationModule
import Definitions.Def_Kourovka_Halfspaces_HalfspaceModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceModule_eventually_shift_mem
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceModule_shift_difference_mem

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceModule
open ValuationModule
variable {Q M : Type} [AddCommGroup Q] [DecidableEq Q]
variable [AddCommGroup M] [Module (GroupRing Q) M]
namespace Kourovka.MetabelianEnumeration.HalfspaceModule
theorem _root_.solution (χ : Q →+ ℝ) (u : Q) (hu : 0 < χ u)
    (V : Submodule (nonnegativeRing χ) M)
    (hspan : Submodule.span (GroupRing Q) (V : Set M) = ⊤)
    (hdiff : ∀ m : M, shift u m - m ∈ V) : V = ⊤ := by
  apply top_unique
  intro m _
  obtain ⟨n, hn⟩ := eventually_shift_mem χ u hu V m (by rw [hspan]; trivial)
  have hd := shift_difference_mem χ u hu.le V m (hdiff m) n
  have h := V.sub_mem hn hd
  simpa only [sub_sub_cancel] using h
end Kourovka.MetabelianEnumeration.HalfspaceModule
