-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SchreierHeights.path_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:20:57.658037+00:00
-- url     : https://prove2.me/submissions/bb5786a9-9fdb-4ca0-abe7-796a767ef539

import Definitions.Def_Kourovka_Halfspaces_SchreierKernel
import Definitions.Def_Kourovka_Halfspaces_SchreierPaths
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_PathIn_append
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_PathIn_start
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_schreierKernelEquiv_of
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_value_mk
import Theorems.Thm_Kourovka_Schreier_Transversal_edge_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_evaluate_of
import Theorems.Thm_Kourovka_Schreier_Transversal_presentationEquiv_of
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_rep
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_rewrite_mk
attribute [local simp] Kourovka.MetabelianEnumeration.SchreierHeights.schreierKernelEquiv_of
attribute [local simp] Kourovka.Schreier.Transversal.edge_vertex
attribute [local simp] Kourovka.Schreier.Transversal.evaluate_of
attribute [local simp] Kourovka.Schreier.Transversal.presentationEquiv_of
attribute [local simp] Kourovka.Schreier.Transversal.rep_rep
attribute [local simp] Kourovka.Schreier.Transversal.rep_vertex
attribute [local simp] Kourovka.Schreier.Transversal.rewrite_mk



set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X : Type*}
namespace Kourovka.MetabelianEnumeration.SchreierHeights
theorem _root_.solution (θ : FreeGroup X →* Multiplicative ℝ) (P : ℝ → Prop)
    (p : ℝ) (xs : List (X × Bool)) (h : PathIn (step θ) P p xs) :
    PathIn (step θ) P (p + value θ (FreeGroup.mk xs)) (FreeGroup.invRev xs) := by
  induction xs generalizing p with
  | nil =>
    change P (p + value θ 1)
    simpa using h
  | cons z xs ih =>
    rcases z with ⟨x, b⟩
    rw [FreeGroup.invRev_cons]
    apply PathIn.append
    · have hh := ih (p + step θ (x, b)) h.2
      cases b <;> simpa [step, letterHeight, mk_cons_false, mk_cons_true, add_assoc] using hh
    · rw [← value_mk, ← FreeGroup.inv_mk, value_inv]
      cases b <;>
        simpa [FreeGroup.invRev, PathIn, step, letterHeight, mk_cons_false, mk_cons_true,
          add_assoc] using And.intro h.2.start h.1
end Kourovka.MetabelianEnumeration.SchreierHeights
