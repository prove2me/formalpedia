-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceLoops.all_differences_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:20:30.363429+00:00
-- url     : https://prove2.me/submissions/f7912c46-bdce-43f9-9f67-3c6e1a7a7b67

import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_difference_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_mul
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_inv
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_evalWord_nil
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_evalWord_cons
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_letter
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_difference_kernel
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_loop_difference_mem
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
theorem _root_.solution (χ : L →+ ℝ) (g : X → E) (u : E)
    (V : Submodule (nonnegativeRing χ) (Additive π.ker))
    (hletters : ∀ x, difference π u (g x) ∈ V)
    (hloops : Subgroup.closure (loopSet π χ g (fun h => h ≤ 0)) = ⊤) :
    ∀ m : Additive π.ker, shift (-(π u).toAdd) m - m ∈ V := by
  let F : AddMonoid.End (Additive π.ker) := {
    toFun := fun m => shift (-(π u).toAdd) m - m
    map_zero' := by simp [shift]
    map_add' := by intro x y; simp only [shift_add]; abel }
  let B : Subgroup π.ker := (V.toAddSubgroup.comap F).toSubgroup'
  have hsub : loopSet π χ g (fun h => h ≤ 0) ⊆ B := by
    intro n hn
    change shift (-(π u).toAdd) (Additive.ofMul n) - Additive.ofMul n ∈ V
    rw [← difference_kernel π hact u n]
    exact loop_difference_mem π hact χ g u V hletters n hn
  have htop : B = ⊤ := by
    apply top_unique
    rw [← hloops]
    exact (Subgroup.closure_le B).2 hsub
  intro m
  have hm : m.toMul ∈ B := by rw [htop]; trivial
  exact hm
end Kourovka.MetabelianEnumeration.HalfspaceLoops
