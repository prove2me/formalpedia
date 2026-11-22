-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceModule.finite_of_shift_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:17:37.057962+00:00
-- url     : https://prove2.me/submissions/30d582e8-6f91-459d-ba74-077ee8786a8f

import Definitions.Def_Kourovka_Modules_ValuationModule
import Definitions.Def_Kourovka_Halfspaces_HalfspaceModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceModule_eq_top_of_shift_difference

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceModule
open ValuationModule
variable {Q M : Type} [AddCommGroup Q] [DecidableEq Q]
variable [AddCommGroup M] [Module (GroupRing Q) M]
namespace Kourovka.MetabelianEnumeration.HalfspaceModule
theorem _root_.solution [DecidableEq M] (χ : Q →+ ℝ) (u : Q) (hu : 0 < χ u)
    (s d : Finset M) (hs : Submodule.span (GroupRing Q) (s : Set M) = ⊤)
    (hdiff : ∀ m : M, shift u m - m ∈
      Submodule.span (nonnegativeRing χ) ((s ∪ d : Finset M) : Set M)) :
    Module.Finite (nonnegativeRing χ) M := by
  classical
  let V := Submodule.span (nonnegativeRing χ) ((s ∪ d : Finset M) : Set M)
  have hspan : Submodule.span (GroupRing Q) (V : Set M) = ⊤ := by
    apply top_unique
    rw [← hs]
    apply Submodule.span_mono
    intro m hm
    exact Submodule.subset_span (Finset.mem_union_left d hm)
  exact ⟨s ∪ d, eq_top_of_shift_difference χ u hu V hspan hdiff⟩
end Kourovka.MetabelianEnumeration.HalfspaceModule
