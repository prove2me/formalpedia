-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SchreierHeights.path_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:20:58.437729+00:00
-- url     : https://prove2.me/submissions/2288e5a6-343a-448e-9fb4-163c7be15ebe

import Definitions.Def_Kourovka_Halfspaces_SchreierKernel
import Definitions.Def_Kourovka_Halfspaces_SchreierPaths
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_schreierKernelEquiv_of
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
theorem _root_.solution (θ : FreeGroup X →* Multiplicative ℝ) {P Q : ℝ → Prop}
    (c : ℝ) {p : ℝ} {xs : List (X × Bool)} (h : PathIn (step θ) P p xs)
    (hc : ∀ z, P z → Q (c + z)) : PathIn (step θ) Q (c + p) xs := by
  induction xs generalizing p with
  | nil => exact hc p h
  | cons x xs ih =>
    exact ⟨hc p h.1, by simpa only [add_assoc] using ih h.2⟩
end Kourovka.MetabelianEnumeration.SchreierHeights
