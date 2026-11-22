-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceLoops.finite_of_lower_loops
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:21:39.122341+00:00
-- url     : https://prove2.me/submissions/35d50594-176a-4f3b-b6a4-952902ff5c3a

import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_difference_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_mul
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_inv
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_evalWord_nil
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_evalWord_cons
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_letter
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_all_differences_mem
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceModule_finite_of_shift_difference
import Theorems.Thm_Kourovka_MetabelianEnumeration_ValuationModule_exists_positive

attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.difference_one
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.height_one
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.height_mul
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.height_inv
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.evalWord_nil
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.evalWord_cons
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.height_letter

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceLoops
open HalfspaceGeometry HalfspaceModule ValuationModule
variable {E L X : Type} [Group E] [AddCommGroup L]
variable (π : E →* Multiplicative L)
variable [IsMulCommutative π.ker]
variable [DecidableEq L] [Module (GroupRing L) (Additive π.ker)]
variable (hact : ∀ (p : E) (n : Additive π.ker),
  conjugate π p n = shift (-(π p).toAdd) n)
include hact
namespace Kourovka.MetabelianEnumeration.HalfspaceLoops
theorem _root_.solution [Fintype X]
    (χ : L →+ ℝ) (hχ : χ ≠ 0) (hπ : Function.Surjective π) (g : X → E)
    [Module.Finite (GroupRing L) (Additive π.ker)]
    (hloops : Subgroup.closure (loopSet π χ g (fun h => h ≤ 0)) = ⊤) :
    Module.Finite (nonnegativeRing χ) (Additive π.ker) := by
  classical
  obtain ⟨v, hv⟩ := exists_positive χ hχ
  obtain ⟨u, hu⟩ := hπ (Multiplicative.ofAdd (-v))
  have hupos : 0 < χ (-(π u).toAdd) := by simpa [hu] using hv
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := GroupRing L) (M := Additive π.ker)
  let d : Finset (Additive π.ker) := Finset.univ.image (fun x => difference π u (g x))
  apply finite_of_shift_difference χ (-(π u).toAdd) hupos s d hs
  apply all_differences_mem π hact χ g u _ _ hloops
  intro x
  apply Submodule.subset_span
  exact Finset.mem_union_right s (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)
end Kourovka.MetabelianEnumeration.HalfspaceLoops
