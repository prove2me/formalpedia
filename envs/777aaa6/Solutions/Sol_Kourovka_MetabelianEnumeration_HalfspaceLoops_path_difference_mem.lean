-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceLoops.path_difference_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:16:55.961282+00:00
-- url     : https://prove2.me/submissions/b1fed990-74f4-4c7d-96a8-1b0a662237a6

import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_difference_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_difference_mul
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_difference_inv
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_conjugate_neg
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_conjugate_conjugate
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_mul
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_inv
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_evalWord_nil
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_evalWord_cons
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_letter
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_PathIn_start
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceModule_shift_mem

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
    (w : List (X × Bool)) (p : E) (hp : difference π u p ∈ V)
    (hw : PathIn (letterHeight (fun x => height π χ (g x)))
      (fun h => h ≤ 0) (height π χ p) w) :
    difference π u (p * evalWord g w) ∈ V := by
  induction w generalizing p with
  | nil => simpa using hp
  | cons z w ih =>
    have hnext : PathIn (letterHeight (fun x => height π χ (g x)))
        (fun h => h ≤ 0) (height π χ (p * letter g z)) w := by
      simpa only [height_mul, height_letter] using hw.2
    have hpnext : difference π u (p * letter g z) ∈ V := by
      rcases z with ⟨x, b⟩
      cases b with
      | true =>
        change difference π u (p * g x) ∈ V
        rw [difference_mul, hact]
        apply V.add_mem hp
        apply shift_mem χ V _ _ _ (hletters x)
        have h := hw.1
        change height π χ p ≤ 0 at h
        simpa only [map_neg, neg_nonneg, height] using h
      | false =>
        change difference π u (p * (g x)⁻¹) ∈ V
        rw [difference_mul, difference_inv, conjugate_neg, conjugate_conjugate, hact]
        apply V.add_mem hp
        apply V.neg_mem
        apply shift_mem χ V _ _ _ (hletters x)
        have h := hnext.start
        change height π χ (p * (g x)⁻¹) ≤ 0 at h
        simpa only [map_neg, neg_nonneg, height] using h
    simpa only [evalWord_cons, mul_assoc] using ih (p * letter g z) hpnext hnext
end Kourovka.MetabelianEnumeration.HalfspaceLoops
