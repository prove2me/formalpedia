-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SchreierHeights.rewrite_mem_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:17:46.765664+00:00
-- url     : https://prove2.me/submissions/96a7309e-6af3-46da-b565-914be3d801fe

import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry
import Definitions.Def_Kourovka_Schreier_PathLifting
import Definitions.Def_Kourovka_Halfspaces_SchreierHeights
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_representative_height
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_PathIn_start
import Theorems.Thm_Kourovka_Schreier_Transversal_edge_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_evaluate_of
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_rep
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_rewrite_mk
attribute [local simp] Kourovka.Schreier.Transversal.edge_vertex
attribute [local simp] Kourovka.Schreier.Transversal.evaluate_of
attribute [local simp] Kourovka.Schreier.Transversal.rep_rep
attribute [local simp] Kourovka.Schreier.Transversal.rep_vertex
attribute [local simp] Kourovka.Schreier.Transversal.rewrite_mk



set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X Q : Type*} [CommGroup Q]
namespace Kourovka.MetabelianEnumeration.SchreierHeights
theorem _root_.solution (π : FreeGroup X →* Q) (χ : Q →* Multiplicative ℝ)
    (S : Transversal π.ker) (P : ℝ → Prop)
    (p : FreeGroup X) (xs : List (X × Bool))
    (hpath : PathIn (letterHeight fun x => value (χ.comp π) (FreeGroup.of x)) P
      (value (χ.comp π) p) xs) :
    S.rewriteWord p xs ∈
      Subgroup.closure (FreeGroup.of '' symbolsIn (χ.comp π) S P) := by
  induction xs generalizing p with
  | nil => exact Subgroup.one_mem _
  | cons z xs ih =>
    rcases z with ⟨x, b⟩
    cases b
    · apply Subgroup.mul_mem
      · apply Subgroup.inv_mem
        apply Subgroup.subset_closure
        refine ⟨S.edge (p * (FreeGroup.of x)⁻¹) x, ?_, rfl⟩
        change P (value (χ.comp π) (S.rep (p * (FreeGroup.of x)⁻¹))) ∧ _
        rw [representative_height]
        constructor
        · simpa only [value_mul, value_inv, letterHeight, Bool.false_eq_true, if_false] using
            hpath.2.start
        · simpa only [edge, value_mul, representative_height, value_inv,
          neg_add_cancel_right] using
            hpath.1
      · apply ih
        simpa only [value_mul, value_inv, letterHeight, Bool.false_eq_true, if_false] using hpath.2
    · apply Subgroup.mul_mem
      · apply Subgroup.subset_closure
        refine ⟨S.edge p x, ?_, rfl⟩
        change P (value (χ.comp π) (S.rep p)) ∧ _
        rw [representative_height]
        constructor
        · exact hpath.1
        · simpa only [edge, value_mul, representative_height, letterHeight, if_true] using hpath.2.start
      · apply ih
        simpa only [value_mul, letterHeight, if_true] using hpath.2
end Kourovka.MetabelianEnumeration.SchreierHeights
