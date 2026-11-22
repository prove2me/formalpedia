-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceLoops.loop_difference_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:18:27.12222+00:00
-- url     : https://prove2.me/submissions/1b025428-04ac-4215-b231-dd81f1c8a488

import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_difference_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_mul
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_inv
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_evalWord_nil
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_evalWord_cons
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_letter
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_path_difference_mem
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
    (hletters : ∀ x, difference π u (g x) ∈ V) (n : π.ker)
    (hn : n ∈ loopSet π χ g (fun h => h ≤ 0)) : difference π u n.val ∈ V := by
  obtain ⟨w, hw, hp⟩ := hn
  have h := path_difference_mem π hact χ g u V hletters w 1
    (by simp) (by simpa [height] using hp)
  simpa only [one_mul, evalWord, hw] using h
end Kourovka.MetabelianEnumeration.HalfspaceLoops
